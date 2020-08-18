package edu.cmu.seai
import scala.util.Random

object Demo extends App {

  def loadFullGolfData(): (DataFrame, Seq[Boolean]) = {
    //   load golf data
    val data = io.Source.fromFile("golf.csv").getLines().map(_.split("\t").toList).toList
    val df = DataFrame.fromCSV(data).dropCol(1).dropCol(2)
    val ycolIdx = df.colNames.size - 1
    val xs = df.dropCol(ycolIdx)
    val ys = df.getCol(ycolIdx).map(_ == df.colValues(ycolIdx).indexOf("yes"))
    (xs, ys)
  }

  def loadCategoricalGolfData(): (DataFrame, Seq[Boolean]) = {
    //   load golf data
    val (xs, ys) = loadFullGolfData()
    (xs.dropCol(1).dropCol(2), ys)
  }

  def loadTitanicData(): (DataFrame, Seq[Boolean]) = {
    // load titanic data
    val data = io.Source.fromFile("titanic2.csv").getLines().map(_.split(",").toList).toList
    val df = DataFrame.fromCSV(data).dropCol(0)
    val ycolIdx = 1
    val xs = df.dropCol(ycolIdx).dropCol(8)
    val ys = df.getCol(ycolIdx).map(_ == 1)
    (xs, ys)
  }


  import Learner._

  println("\n# load data")
  val (xs, ys) = loadCategoricalGolfData()


  println("\n# look at the data")
  println(xs)
  println(ys)

  println("\n# best single prediction without any tree")
  println(fitOutcome(ys))

  println("\n# all predicates that could be used in learning")
  println(genAllPreds(xs))

  println("\n# learn a model on the full dataset and print it")
  println(learn(xs, ys, 100))


  import ModelQuality._

  {
    println("\n# evaluate accuracy on the full train set")
    val model = learn(xs, ys, 3)
    val pred_ys = model.predict(xs)
    println(f"Accuracy: ${accuracy(pred_ys, ys)}%.4f")
  }

  {
    println("\n# split train and validation set (80-20, randomly)")
    val (trainX, trainY, testX, testY) = learnTestSplit(xs, ys, .8)
    println(s"${trainX.data.size} training size, ${testX.data.size} test size")
    val model = learn(trainX, trainY, 3)
    val pred_trainY = model.predict(trainX)
    val pred_testY = model.predict(testX)
    println(f"Accuracy on training data: ${accuracy(pred_trainY, trainY)}%.4f")
    println(f"Accuracy on test data: ${accuracy(pred_testY, testY)}%.4f")
  }

  {
    println("\n# repeat training at different maxdepth hyperparameters")
    val (trainX, trainY, testX, testY) = learnTestSplit(xs, ys, .8)
    println(s"${trainX.data.size} training size, ${testX.data.size} test size")
    for (maxDepth <- 1 until 10) {
      val model = learn(trainX, trainY, maxDepth)
      val pred_trainY = model.predict(trainX)
      val pred_testY = model.predict(testX)
      println(f"Accuracy on training data: ${accuracy(pred_trainY, trainY)}%.4f")
      println(f"Accuracy on test data: ${accuracy(pred_testY, testY)}%.4f")
    }
  }

  println("\n# perform crosvalidation (20 random splits)")
  val (trainingAccuracy, validationAccuracy) = crossValidation(xs, ys, (x, y) => learn(x, y, 3), accuracy, .8, 20)
  println(f"Average accuracy on training data: $trainingAccuracy%.4f")
  println(f"Average accuracy on test data: $validationAccuracy%.4f")

  println("\n# report crossvalidation results at different maxDepth hyperparameters")
  for (deg <- Seq(0, 1, 2, 3, 4, 5, 8, 10, 20, 100)) {
    val (trainingAccuracy, validationAccuracy) = crossValidation(xs, ys, (x, y) => learn(x, y, deg), accuracy, .8, 10)
    println(f"$deg: $trainingAccuracy%.4f $validationAccuracy%.4f")
  }


}


/**
 * Decision tree structure, consisting of Decisions and Outcomes; Decisions have Predicates
 */
trait Node {
  override def toString() = print(0)

  def print(indent: Int): String

  // outcome only for each row of the dataframe
  def predict(df: DataFrame): Seq[Boolean] = predictOutcomeAndConfidence(df).map(_._1)

  // outcome, confidence pair for each row of the dataframe
  def predictOutcomeAndConfidence(df: DataFrame): Seq[(Boolean, Double)] = df.data.map(predictOutcomeAndConfidence)

  // outcome, confidence pair for a single data point
  def predictOutcomeAndConfidence(row: Seq[Int]): (Boolean, Double)
}

case class Decision(pred: Pred, left: Node, right: Node, gain: Double) extends Node {
  def print(indent: Int): String = "  " * indent + f"IF $pred // gain $gain%.4f\n" + left.print(indent + 1) + right.print(indent + 1)

  def predictOutcomeAndConfidence(row: Seq[Int]) =
    if (pred.select(row)) left.predictOutcomeAndConfidence(row) else right.predictOutcomeAndConfidence(row)
}

case class Outcome(outcome: Boolean, confidence: Float) extends Node {
  def print(indent: Int): String = "  " * indent + outcome.toString() + f" ($confidence%.3f)\n"

  def predictOutcomeAndConfidence(row: Seq[Int]) = (outcome, confidence)
}

/**
 * Predicates split the data for one decision. Here different versions for Categorical and Numeric data
 */
trait Pred {
  def select(row: Seq[Int]): Boolean
}

class PredCat(val colIdx: Int, val valIdx: Int, colName: String, valsStr: Seq[String]) extends Pred {
  override def toString(): String = s"$colName ∈ [${valsStr.mkString(",")}]"

  def select(row: Seq[Int]): Boolean = row(colIdx) <= valIdx
}

class PredNum(val colIdx: Int, val v: Int, colName: String) extends Pred {
  override def toString(): String = s"$colName <= $v"

  def select(row: Seq[Int]): Boolean = row(colIdx) <= v
}


object Learner {
  //another hyperparameter on when to stop splitting
  val MIN_GAIN = 0.0001

  // predicts the last column based on all the ones before
  def learn(Xs: DataFrame, Ys: Seq[Boolean], max_depth: Int = Int.MaxValue): Node =
    ID3(Xs, genAllPreds(Xs), Ys, max_depth)

  def ID3(xs: DataFrame, preds: Set[Pred], ys: Seq[Boolean], max_depth: Int): Node = {
    // if all outcomes are the same, report confident decision
    if (ys.forall(x => x)) return Outcome(true, 1)
    if (ys.forall(x => !x)) return Outcome(false, 1)
    // if no more predicates left, fit best decision we have
    if (preds.isEmpty || max_depth <= 0) return fitOutcome(ys)

    // compute the gain for every possible predicate
    val allGains = preds.map(p => (gain(xs, ys, p.select), p))
    // pick the best predicate
    val (bestGain, bestPred) = allGains.maxBy(_._1)
    // if improvement is too small, stop
    if (bestGain < MIN_GAIN) return fitOutcome(ys)

    //split with the best predicate
    val (leftX, leftY, rightX, rightY) = split(xs, ys, bestPred)
    // recursively further split both subtrees until stopping criteria is reached
    Decision(bestPred, ID3(leftX, preds - bestPred, leftY, max_depth - 1), ID3(rightX, preds - bestPred, rightY, max_depth - 1), bestGain)
  }


  // which is the more common outcome, true or false?
  def moreCommon(ys: Seq[Boolean]): Boolean =
    ys.count(x => x) >= ys.count(x => !x)

  // report the more common outcome as a result together with the corresponding confidence (percentage of all outcomes)
  def fitOutcome(ys: Seq[Boolean]): Outcome =
    Outcome(moreCommon(ys), (ys.count(x => x) max ys.count(x => !x)).toFloat / ys.size)

  //compute entropy, see a textbook
  def entropy(ys: Seq[Boolean]): Double = {
    if (ys.isEmpty) return 0
    val p_true = ys.count(x => x).toDouble / ys.size
    val p_false = ys.count(x => !x).toDouble / ys.size
    val l2 = math.log(2)

    def log2(p: Double): Double = if (p == 0) 0 else math.log(p) / l2

    -p_true * log2(p_true) - p_false * log2(p_false)
  }

  //compute information gain based on entropy improvement, see a textbook
  def gain(xs: DataFrame, ys: Seq[Boolean], pred: Seq[Int] => Boolean): Double = {
    val leftRows = xs.data.map(pred)
    val leftYs = (leftRows zip ys).filter(_._1).map(_._2)
    val rightYs = (leftRows zip ys).filterNot(_._1).map(_._2)

    entropy(ys) - (leftYs.size.toDouble / ys.size) * entropy(leftYs) - (rightYs.size.toDouble / ys.size) * entropy(rightYs)
  }

  // list all possible predicates,
  def genAllPreds(xs: DataFrame): Set[Pred] = {
    val categoricalPredicates =
      for (colIdx <- xs.colNames.indices; if !xs.colIsNumeric(colIdx); valIdx <- xs.colValues(colIdx).indices.dropRight(1)) yield
        new PredCat(colIdx, valIdx, xs.colNames(colIdx), xs.colValues(colIdx).take(valIdx + 1))
    val numericPredicates =
      for (colIdx <- xs.colNames.indices; if xs.colIsNumeric(colIdx); v <- xs.getCol(colIdx).distinct) yield
        new PredNum(colIdx, v.toInt, xs.colNames(colIdx))
    (categoricalPredicates ++ numericPredicates).toSet
  }


  // split both x and y according to a predicate
  def split(xs: DataFrame, ys: Seq[Boolean], pred: Pred): (DataFrame, Seq[Boolean], DataFrame, Seq[Boolean]) = {
    val d = xs.data.zip(ys).map(d => (d._1, d._2, pred.select(d._1)))
    val leftX = d.filter(_._3).map(_._1)
    val rightX = d.filterNot(_._3).map(_._1)
    val leftY = d.filter(_._3).map(_._2)
    val rightY = d.filterNot(_._3).map(_._2)
    (new DataFrame(xs.colNames, xs.colIsNumeric, xs.colValues, leftX), leftY,
      new DataFrame(xs.colNames, xs.colIsNumeric, xs.colValues, rightX), rightY)

  }


}


/**
 * several functions to compute accuracy
 */
object ModelQuality {
  //compare actual and predicted values
  def accuracy(predicted: Seq[Boolean], actual: Seq[Boolean]): Double = {
    assert(predicted.length == actual.length)
    (predicted zip actual).count(s => s._1 == s._2).toDouble / actual.length
  }

  //randomly split a dataset (both x and y)
  def learnTestSplit(x: DataFrame, y: Seq[Boolean], ratio: Double): (DataFrame, Seq[Boolean], DataFrame, Seq[Boolean]) = {
    assert(x.data.length == y.length)
    val trainSize = (ratio * y.length).toInt
    val selector = Random.shuffle(Seq.fill(trainSize)(true) ++ Seq.fill(y.length - trainSize)(false))

    val d = x.data.zip(y).zip(selector)
    val leftX = d.filter(_._2).map(_._1._1)
    val rightX = d.filterNot(_._2).map(_._1._1)
    val leftY = d.filter(_._2).map(_._1._2)
    val rightY = d.filterNot(_._2).map(_._1._2)
    (new DataFrame(x.colNames, x.colIsNumeric, x.colValues, leftX), leftY,
      new DataFrame(x.colNames, x.colIsNumeric, x.colValues, rightX), rightY)
  }

  // crossvalidation with repeated random splits (MonteCarlo)
  def crossValidation(x: DataFrame, y: Seq[Boolean], learn: (DataFrame, Seq[Boolean]) => Node, eval: (Seq[Boolean], Seq[Boolean]) => Double, ratio: Double = .8, rounds: Int = 20): (Double, Double) = {
    val results = for (round <- 0 to rounds) yield {
      val (trainX, trainY, testX, testY) = learnTestSplit(x, y, ratio)
      val model = learn(trainX, trainY)
      val pred_trainY = model.predict(trainX)
      val pred_testY = model.predict(testX)
      (eval(pred_trainY, trainY), eval(pred_testY, testY))
    }
    (results.map(_._1).sum / results.size, results.map(_._2).sum / results.size)
  }

}


/**
 * helper class to represent a table
 */
class DataFrame(val colNames: Seq[String], val colIsNumeric: Seq[Boolean], val colValues: Seq[Seq[String]], val data: Seq[Seq[Int]]) {
  assert(colNames.length == colIsNumeric.length)
  assert(colNames.length == colValues.length)
  assert(data.forall(_.length == colNames.length))

  def colIdxs = colNames.indices

  def getCol(idx: Int): Seq[Int] = data.map(_ (idx))

  def dropCol(idx: Int): DataFrame =
    new DataFrame(colNames.take(idx) ++ colNames.drop(idx + 1),
      colIsNumeric.take(idx) ++ colIsNumeric.drop(idx + 1),
      colValues.take(idx) ++ colValues.drop(idx + 1),
      data.map(r => r.take(idx) ++ r.drop(idx + 1))
    )

  override def toString(): String = {
    val s = new StringBuilder
    s.append(colNames.mkString("", ",", "\n"))
    s.append(colIsNumeric.map(if (_) "num" else "cat").mkString("", ",", "\n"))
    data.take(10).foreach(r =>
      s.append(printRow(r) + "\n")
    )
    if (data.size > 10) s.append("...\n")
    s.toString()
  }

  private def printRow(r: Seq[Int]) =
    r.zipWithIndex.map(x => if (colIsNumeric(x._2)) x._1 else colValues(x._2)(x._1)).mkString(",")

  def split(pred: Seq[Int] => Boolean): (DataFrame, DataFrame) = {
    val d = data.map(d => (d, pred(d)))
    val left = d.filter(_._2).map(_._1)
    val right = d.filterNot(_._2).map(_._1)
    (new DataFrame(colNames, colIsNumeric, colValues, left),
      new DataFrame(colNames, colIsNumeric, colValues, right))
  }

}

object DataFrame {
  def fromCSV(raw: List[List[String]]): DataFrame = {
    val cols = raw.head
    raw.foreach(r => assert(r.size == cols.size, s"$r with ${r.size}!=${cols.size}"))

    val colValues =
      for (i <- cols.indices) yield
        raw.tail.map(_ (i)).distinct
    val colIsNumeric =
      for (i <- cols.indices) yield
        raw.tail.forall(s => s(i).isEmpty || s(i).toDoubleOption.isDefined)
    val data: Seq[Seq[Int]] = raw.tail.map(row =>
      row.zipWithIndex.map({ case (v, idx) => if (colIsNumeric(idx)) v.toDoubleOption.getOrElse(-1d).toInt else colValues(idx).indexOf(v) })
    )
    new DataFrame(cols, colIsNumeric, colValues, data)
  }
}
