package org.tygus.suslik.interaction

import java.util.concurrent.ArrayBlockingQueue
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}
import org.slf4j.Logger
import upickle.default.{macroRW, ReadWriter => RW}

import akka.{Done, NotUsed}
import akka.actor.typed.ActorSystem
import akka.actor.typed.scaladsl.Behaviors
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.ws.{Message, TextMessage}
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.server.Directives._
import akka.stream.scaladsl.{Flow, Sink, Source}

import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.report.ProofTraceJson
import org.tygus.suslik.report.ProofTraceJson.GoalEntry
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.tactics.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil}


class SynthesisServer {

  val config: SynConfig = SynConfig()

  /* Server configuration */
  protected def port(implicit system: ActorSystem[_]): Int =
    system.settings.config.getInt("suslik.server.port");

  def start(): Unit = {
    val root = Behaviors.setup[Nothing] { context =>
      implicit val system: ActorSystem[_] = context.system
      startHttpServer(routes, port)
      Behaviors.empty
    }
    ActorSystem[Nothing](root, "SynthesisServer")
  }

  /**
    * Server startup boilerplate.
    */
  private def startHttpServer(routes: Route, port: Int)(implicit system: ActorSystem[_]): Unit = {
    import system.executionContext
    Http().newServerAt("localhost", port).bind(routes)
      .onComplete {
        case Success(binding) =>
          val address = binding.localAddress
          system.log.info("Server online at http://{}:{}/", address.getHostString, address.getPort)
        case Failure(ex) =>
          system.log.error("Failed to bind HTTP endpoint, terminating system", ex)
          system.terminate()
      }
  }

  def go(session: SynthesisRunnerUtil): String = {
    val dir = "./src/test/resources/synthesis/all-benchmarks/sll" /** @todo */
    val fn = "free.syn"
    session.synthesizeFromFile(dir, fn, config).toString()
  }

  private def routes(implicit system: ActorSystem[_]) = {
    import system.executionContext
    concat(
      pathSingleSlash {
        concat(
          handleWebSocketMessages({
            val session = new ClientSessionSynthesis()
            new Thread(() => go(session)).start()
            session.wsFlow
          }),
          get {
            new Thread(() => go(new AsyncSynthesisRunner)).start(); complete(".")
          }
        )
      }
    )
  }
}

object SynthesisServer {
  def main(args: Array[String]): Unit = {
    val server = new SynthesisServer
    server.start()
  }
}

/**
  * A synthesizer that sends and receives choices via async queues.
  * Data is serialized in and out using a JSON format.
  */
class AsyncSynthesisRunner extends SynthesisRunnerUtil {
  import upickle.default.{Writer, write}
  import AsyncSynthesisRunner._

  val inbound = new ArrayBlockingQueue[String](1)
  val outbound = new ArrayBlockingQueueWithCancel[String](1)

  /**
    * Creates a `PhasedSynthesizer` that expands goals based on input sent
    * from the client (through `inbound`) and reports everything back to the
    * client in JSON format (through `outbound`).
    * @param env synthesis environment
    * @return a configured `Synthesis` instance
    */
  override def createSynthesizer(env: Environment): Synthesis = {
    val tactic =
      new PhasedSynthesis(env.config) {
        override def filterExpansions(allExpansions: Seq[Rules.RuleResult]): Seq[Rules.RuleResult] = {
          allExpansions.find(_.subgoals.isEmpty) match {
            case Some(fin) => Seq(fin)
            case _ =>
              outbound.put(serializeChoices(allExpansions))
              val choice = inbound.take()
              allExpansions.filter(_.subgoals.exists(goal => goal.label.pp.contains(choice)))
          }
        }
      }
    val trace = new ProofTraceJson {
      override protected def writeObject[T](t: T)(implicit w: Writer[T]): Unit =
        outbound.put(write(t))
    }
    new Synthesis(tactic, log, trace)
  }

  /**
    * Wraps parent implementation, reporting success or failure to the client.
    * @todo make results be JSON
    */
  override def synthesizeFromSpec(testName: String, text: String, out: String,
                                  params: SynConfig): List[Statements.Procedure] = {
    try {
      val ret = super.synthesizeFromSpec(testName, text, out, params)
      outbound.put(ret.toString)
      ret
    }
    catch { case e: Throwable => outbound.put(e.toString); throw e }
  }

  protected def serializeChoices(allExpansions: Seq[Rules.RuleResult]): String =
    write(allExpansions.map(ExpansionChoice.from))
}

object AsyncSynthesisRunner {

  class ArrayBlockingQueueWithCancel[E](capacity: Int)
      extends ArrayBlockingQueue[E](capacity) {
    private var waiting: Option[Thread] = None
    override def take(): E = {
      assert(waiting.isEmpty)  /* allow at most one consumer thread */
      waiting = Some(Thread.currentThread())
      try super.take() finally { waiting = None }
    }
    def cancel() { waiting foreach (_.interrupt()) }
  }

  type GoalLabel = String

  case class ExpansionChoice(from: Set[GoalLabel],
                             rule: String,
                             subgoals: Seq[GoalEntry])

  object ExpansionChoice {
    def from(rr: Rules.RuleResult): ExpansionChoice =
      ExpansionChoice(rr.subgoals.flatMap(_.parent).map(_.label.pp).toSet,
        rr.rule.toString,
        rr.subgoals.map(GoalEntry(_)))

    implicit val readWriter: RW[ExpansionChoice] = macroRW
  }
}

/**
  * Connects `AsyncSynthesisRunner` to an HTTP client.
  */
class ClientSessionSynthesis(implicit ec: ExecutionContext) extends AsyncSynthesisRunner {

  val logger: Logger = org.slf4j.LoggerFactory.getLogger(getClass)

  def subscribe: Source[String, _] =
    Source.unfoldAsync(())(_ => Future {
      try Some((), outbound.take())
      catch { case _: InterruptedException => None }
    })

  def offer: Sink[String, Future[Done]] =
    Sink.foreachAsync[String](1)(s => Future { inbound.put(s) })

  def done(d: Done): Unit = {
    outbound.cancel()
    logger.info(s"client session ended; $d")
  }

  def wsFlow: Flow[Message, Message, NotUsed] =
    Flow.fromSinkAndSource(Flow[Message].mapConcat {
        case m: TextMessage.Strict => println(m.text); List(m.text)
        case _ => println("some other message"); Nil
      }.to(offer.mapMaterializedValue(m => m.foreach(done))),
      subscribe.map(TextMessage(_)))
}