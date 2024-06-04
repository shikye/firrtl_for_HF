// Modified version,
// Instrumentation for control coverage

package coverage

import java.io.{File, PrintWriter}

import firrtl._
import firrtl.ir._
import firrtl.Mappers._

import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.collection.{Map, Set, mutable}

object moduleInfo {
  def apply(mod: DefModule, gLedger: graphLedger): moduleInfo = {
    val ctrlSrcs = gLedger.findMuxSrcs
    val muxSrcs = gLedger.getMuxSrcs
    val insts = gLedger.getInstances
    val regs = gLedger.findRegs
    val vecRegs = gLedger.findVecRegs
    val dirInRegs = gLedger.findDirInRegs

    new moduleInfo(mod.name, ctrlSrcs, muxSrcs, insts, regs, vecRegs, dirInRegs)
  }
}

class moduleInfo(val mName: String,
                 val ctrlSrcs: Map[String, Set[Node]],
                 val muxSrcs: Map[Mux, Set[String]],
                 val insts: Set[WDefInstance],
                 val regs: Set[DefRegister],
                 val vecRegs: Set[Tuple3[Int, String, Set[String]]],
                 val dirInRegs: Set[DefRegister]) {

  var covSize: Int = 0
  var regNum: Int = 0
  var ctrlRegNum: Int = 0
  var muxNum: Int = 0
  var muxCtrlNum: Int = 0
  var regBitWidth: Int = 0
  var ctrlRegBitWidth: Int = 0
  var ctrlBitWidth: Int = 0
  var assertReg: Option[DefRegister] = None

  var regState: Option[DefRegister] = None
  var covSum: Option[DefRegister] = None
  var covMap: Option[DefRegister] = None

  def printInfo(): Unit = {
    print(s"${mName} Information\n")
  }

  def saveCovResult(instrCov: InstrCov): Unit = {
    covSize = instrCov.covMapSize
    regNum = regs.size
    ctrlRegNum = ctrlSrcs("DefRegister").size
    regBitWidth = regs.toSeq.map(reg => reg.tpe match {
      case utpe: UIntType => utpe.width.asInstanceOf[IntWidth].width.toInt
      case stpe: SIntType => stpe.width.asInstanceOf[IntWidth].width.toInt
      case _ => throw new Exception(s"${reg.name} does not have IntType\n")
    }).sum

    ctrlRegBitWidth = ctrlSrcs("DefRegister").toSeq.map(reg => {
      reg.node.asInstanceOf[DefRegister].tpe match {
        case utpe: UIntType => utpe.width.asInstanceOf[IntWidth].width.toInt
        case stpe: SIntType => stpe.width.asInstanceOf[IntWidth].width.toInt
        case _ => throw new Exception(s"${reg.name} does not have IntType\n")
      }
    }).sum

    ctrlBitWidth = instrCov.totBitWidth
    muxNum = muxSrcs.size
    muxCtrlNum = muxSrcs.map(_._1.cond.serialize).toSet.size
  }
}

class regCoverage extends Transform {

  def inputForm: LowForm.type = LowForm
  def outputForm: LowForm.type = LowForm

  val TargetModules = mutable.Set[DefModule]()
  val InstSet = mutable.Queue[DefInstance]()

  val moduleInfos = mutable.Map[String, moduleInfo]()
  var totNumOptRegs = 0


  def findInstance(s: FirrtlNode): Unit = {
    s match {
      case DefInstance(_, name, module, _) =>
        InstSet.enqueue(DefInstance(NoInfo, name, module, UnknownType))
      case stmt: Statement =>
        stmt foreachStmt findInstance
      case other => Unit
    }
  }


  def execute(state: CircuitState): CircuitState = {
    val circuit = state.circuit
    val TargetModuleName = "RocketTile"

    print("==================== Finding Target Modules ====================\n")
    for (m <- circuit.modules) {
      if(m.name == TargetModuleName) {
        print(s"Top Module: ${m.name} found\n")
        TargetModules += m
        
        //大statement夹杂小statement******
        m foreachStmt findInstance
      }
    }

    while(InstSet.nonEmpty) {
      val inst = InstSet.dequeue()
      val instModule = circuit.modules.find(_.name == inst.module).get
      if(!TargetModules.contains(instModule)) {
        print(s"Target Module: ${instModule.name} found\n")
        TargetModules += instModule
        instModule foreachStmt findInstance
      }
    }

    print("==================== Finding Control Registers ====================\n")

    for (m <- circuit.modules) {

      val gLedger = new graphLedger(m)

      gLedger.parseModule
      moduleInfos(m.name) = moduleInfo(m, gLedger)
      gLedger.printLog()
    }

    print("===================================================================\n")

    print("====================== Instrumenting Coverage =====================\n")

    
    val TargetNames = TargetModules.map(_.name)   //Circuit中的Modules由于插桩而变化，所以依靠name来获取


    val extModules = circuit.modules.filter(_.isInstanceOf[ExtModule]).map(_.name)
    val instrCircuit = circuit map { m: DefModule =>
      if(TargetNames.contains(m.name)){
        val instrCov = new InstrCov(m, moduleInfos(m.name), extModules)
        val mod = instrCov.instrument()
        totNumOptRegs = totNumOptRegs + instrCov.numOptRegs
        instrCov.printLog()
        moduleInfos(m.name).saveCovResult(instrCov)
        mod
      }else{
        m
      }
    }

    print("===================================================================\n")

    print("====================== Instrumenting metaAssert ===================\n")
    


    val assertCircuit = instrCircuit map { m: DefModule =>
      if(TargetNames.contains(m.name)){
        val instrAssert = new InstrAssert(m, moduleInfos(m.name))
        val mod = instrAssert.instrument()
        mod
      }else{
        m
      }
    }

    print("===================================================================\n")

    print("====================== Instrumenting MetaReset ====================\n")

    val metaResetCircuit = assertCircuit map { m: DefModule =>
      if(TargetNames.contains(m.name)){
        // println("here has modules in metareset")
        val instrReset = new InstrReset(m, moduleInfos(m.name))
        val mod = instrReset.instrument()
        instrReset.printLog()
        mod
      }else{
        m
      }
    }

    print("===================================================================\n")



    val findPath = mutable.Stack[String]()
    //深度优先遍历找到从m到TargetModule的路径,需要递归遍历m的每一个inst,知道找到一条从m到TargetModule的路径，并存储在findPath中
    def findPathToTarget(m: DefModule): Boolean = {
      if(m.name == TargetModuleName){
        findPath.push(m.name)
        return true
      }else{
        val insts = moduleInfos(m.name).insts
        for(inst <- insts){
          val instModule = circuit.modules.find(_.name == inst.module)
          if(instModule != None){
            if(findPathToTarget(instModule.get)){
              findPath.push(m.name)
              return true
            }
          }
        }
        return false
      }
    }
    
    println("circuit main is " + circuit.main)
    findPathToTarget(circuit.modules.find(_.name == circuit.main).get)
    println(findPath)

    def updateConnetTargetandTopCircuit(circuit: Circuit): Circuit = {
      if (findPath.size <= 1) {
        circuit
      } else {
        val TopModuleName = findPath.pop()
        val SubModuleName = findPath.top
        println("TopModuleName is " + TopModuleName + " SubModuleName is " + SubModuleName)
        
        val SubInst = moduleInfos(TopModuleName).insts.find(_.module == SubModuleName).get
        val TopPorts = circuit.modules.find(_.name == TopModuleName).get.ports

        val covSumPort = Port(NoInfo, "io_covSum", Output, UIntType(IntWidth(16)))
        val metaAssertPort = Port(NoInfo, "metaAssert", Output, UIntType(IntWidth(1)))
        val metaResetPort = Port(NoInfo, "metaReset", Input, UIntType(IntWidth(1)))

        val ConcovSum = Connect(NoInfo, WRef(covSumPort), WSubField(WRef(SubInst), "io_covSum"))
        val ConmetaAssert = Connect(NoInfo, WRef(metaAssertPort), WSubField(WRef(SubInst), "metaAssert"))
        val ConmetaReset = Connect(NoInfo, WRef(metaResetPort), WSubField(WRef(SubInst), "metaReset"))

        val ports = TopPorts :+ covSumPort :+ metaAssertPort :+ metaResetPort

        val updatedCircuit = circuit map { m: DefModule =>
          m match {
            case m: Module if m.name == TopModuleName =>
              val newBlock = Block(m.body.asInstanceOf[Block].stmts :+ ConcovSum :+ ConmetaAssert :+ ConmetaReset)
              Module(m.info, m.name, ports, newBlock)
            case _ => m
          }
        }
        updateConnetTargetandTopCircuit(updatedCircuit)
      }
    }

    val ConnetTargetandTopCircuit = updateConnetTargetandTopCircuit(metaResetCircuit)


    print("\n====================== Instrumentation Summary ==================\n")
    printSummary(TargetModuleName)
    print("===================================================================\n")

    /* Dump hierarchy of the modules to instrument system tasks  */
    val hierWriter = new PrintWriter(new File(s"${ConnetTargetandTopCircuit.main}_hierarchy.txt"))
    for ((mName, mInfo) <- moduleInfos) {
      val insts = mInfo.insts
      hierWriter.write(s"$mName\t${insts.size}\t${mInfo.covSize}\n")
      insts.map(inst => hierWriter.write(s"\t${inst.module}\t${inst.name}\n"))
    }
    hierWriter.close()

    state.copy(ConnetTargetandTopCircuit)

  }

  def printSummary(topName: String) : Unit = {
    assert(moduleInfos.size > 0, "printSummary must be called after instrumentation\n")

    val moduleNums: Map[String, Int] = moduleInfos.map(tuple => {
      (tuple._1, findModules(topName, tuple._1))
    }).toMap

    val totRegNum = moduleInfos.foldLeft(0)((totNum, tuple) => {
      totNum + (tuple._2.regNum * moduleNums(tuple._1))
    })

    val totCtrlRegNum = moduleInfos.foldLeft(0)((totNum, tuple) => {
      totNum + (tuple._2.ctrlRegNum * moduleNums(tuple._1))
    })

    val totMuxNum = moduleInfos.foldLeft(0)((totNum, tuple) => {
      totNum + (tuple._2.muxNum * moduleNums(tuple._1))
    })

    val totRegBitWidth = moduleInfos.foldLeft(0)((totBitWidth, tuple) => {
      totBitWidth + (tuple._2.regBitWidth * moduleNums(tuple._1))
    })

    val totCtrlRegBitWidth = moduleInfos.foldLeft(0)((totBitWidth, tuple) => {
      totBitWidth + (tuple._2.ctrlRegBitWidth * moduleNums(tuple._1))
    })

    val totCtrlBitWidth_optimized = moduleInfos.foldLeft(0)((totBitWidth, tuple) => {
      totBitWidth + (tuple._2.ctrlBitWidth * moduleNums(tuple._1))
    })

    val totMuxBitWidth = totMuxNum

    val totMuxCtrlBitWidth = moduleInfos.foldLeft(0)((totBitWidth, tuple) => {
      totBitWidth + (tuple._2.muxCtrlNum * moduleNums(tuple._1))
    })

    print(s"Total number of registers: ${totRegNum}\n" +
      s"Total number of control registers: ${totCtrlRegNum}\n" +
      s"Total number of muxes: ${totMuxNum}\n" +
      s"Total number of optimized registers: ${totNumOptRegs}\n" +
      s"Total bit width of registers: ${totRegBitWidth}\n" +
      s"Total bit width of control registers: ${totCtrlRegBitWidth}\n" +
      s"Optimized total bit width of control registers: ${totCtrlBitWidth_optimized}\n" +
      s"Total bit width of muxes: ${totMuxBitWidth}\n" +
      s"Total bit width of muxes: ${totMuxCtrlBitWidth}\n"
    )
  }

  def findModules(topName: String, moduleName: String): Int = {
    if (topName == moduleName) 1
    else {
      moduleInfos(topName).insts.foldLeft(0)((num, inst) => {
        num + findModules(inst.module, moduleName)
      })
    }
  }
}
