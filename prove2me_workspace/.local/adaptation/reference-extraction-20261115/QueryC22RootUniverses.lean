/-
Narrow supplementary query, not yet compiled. The 96-module graph already
passed in ci-012771-ee109b3e; do not rerun graph extraction for this query.

MCP-CI leaf/file entry; import the same accepted C22 environment/LEAN_PATH.
Output directory: structured environment.REFERENCE_ROOT_TYPES_DIR (absolute).
Each root gets a separate default-heartbeat run_meta and JSON output file.
-/
import Lean
import Iut.Implication.Corollary22

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true

open Lean
namespace C22RootUniverses

def queryRoot (name : Name) (outputFile : String) : MetaM Unit := do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Wrong original-source query compiler: {Lean.versionString}"
  let ci ← getConstInfo name
  let env ← getEnv
  let sourceModule : Option Name := do
    let index ← env.getModuleIdxFor? name
    env.header.moduleNames[index.toNat]?
  let telescope ← Lean.Meta.forallTelescope ci.type fun xs result => do
    let mut binders : Array Json := #[]
    for x in xs do
      let declaration ← x.fvarId!.getDecl
      binders := binders.push (Json.mkObj [
        ("name", Json.str declaration.userName.toString),
        ("binderInfo", Json.str (reprStr declaration.binderInfo)),
        ("type", Json.str (← Lean.Meta.ppExpr declaration.type).pretty)])
    return Json.mkObj [("binders", Json.arr binders),
      ("result", Json.str (← Lean.Meta.ppExpr result).pretty)]
  let axioms ← collectAxioms name
  let result := Json.mkObj [
    ("schema", Json.str "c22-root-universe-query-v1"),
    ("graphJobId", Json.str "ci-012771-ee109b3e"),
    ("compilerVersion", Json.str Lean.versionString),
    ("name", Json.str name.toString),
    ("module", sourceModule.map (Json.str ·.toString) |>.getD Json.null),
    -- Preserve kernel declaration order; do not sort universe parameters.
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("ppUniverses", toJson true),
    ("elaboratedType", Json.str (← Lean.Meta.ppExpr ci.type).pretty),
    ("elaboratedTelescope", telescope),
    ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString)),
    ("hasSorryAx", toJson (axioms.contains `sorryAx)),
    ("unexpectedAxioms", toJson ((axioms.filter fun ax =>
      !#[`propext, `Classical.choice, `Quot.sound].contains ax).map Name.toString))]
  IO.FS.writeFile outputFile (result.pretty ++ "\n")
  logInfo s!"Root universe/type/axiom query: {name} → {outputFile}"

def outputDirectory : IO String := do
  let directory := (← IO.getEnv "REFERENCE_ROOT_TYPES_DIR").getD
    "/tmp/p2m-reference-skeleton-tool-20261115/c22-root-universes"
  unless (System.FilePath.mk directory).isAbsolute do
    throw (IO.userError "REFERENCE_ROOT_TYPES_DIR must be absolute")
  IO.FS.createDirAll directory
  return directory

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.Theorem110Invariants.theorem110 (directory ++ "/theorem110.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.ThetaDataExistence (directory ++ "/theta-data-existence.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.Corollary22Inputs.c2 (directory ++ "/corollary22-c2.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.ThetaDataExistence.thetaData (directory ++ "/theta-data-field.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.ThetaDataExistence.mk (directory ++ "/theta-data-constructor.json")

end C22RootUniverses

#print axioms Iut.Theorem110Invariants.theorem110
#print axioms Iut.ThetaDataExistence
#print axioms Iut.Corollary22Inputs.c2
