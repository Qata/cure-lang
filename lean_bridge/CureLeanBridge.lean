import Lean

open Lean

def protocolVersion : Nat := 1

def jsonOk (fields : List (String × Json)) : Json :=
  Json.mkObj (("status", Json.str "ok") :: fields)

def jsonError (message : String) : Json :=
  Json.mkObj [
    ("status", Json.str "error"),
    ("error", Json.str message)
  ]

def jsonDiagnostics (diagnostics : Json) : Json :=
  Json.mkObj [
    ("status", Json.str "error"),
    ("diagnostics", diagnostics)
  ]

def getString? (json : Json) (key : String) : Option String := do
  let value ← json.getObjVal? key |>.toOption
  value.getStr? |>.toOption

def jsonField (json : Json) (key : String) : Except String Json :=
  json.getObjVal? key

def stringField (json : Json) (key : String) : Except String String := do
  (← jsonField json key).getStr?

def natField (json : Json) (key : String) : Except String Nat := do
  (← jsonField json key).getNat?

def arrayField (json : Json) (key : String) : Except String (Array Json) := do
  (← jsonField json key).getArr?

def levelOfNat : Nat → Level
  | 0 => levelZero
  | n + 1 => Level.succ (levelOfNat n)

def cureSort (level : Nat) : Expr :=
  mkSort (Level.succ (levelOfNat level))

def cureName (name : String) : Name :=
  Name.str (Name.mkSimple "Cure") name

abbrev TranslateM := ExceptT String CoreM
abbrev TranslateMetaM := ExceptT String Meta.MetaM

def failTranslate (err : String) : TranslateM α :=
  ExceptT.mk <| pure <| Except.error err

def liftJson : Except String α → TranslateM α
  | Except.ok value => pure value
  | Except.error err => failTranslate err

def failTranslateMeta (err : String) : TranslateMetaM α :=
  ExceptT.mk <| pure <| Except.error err

def liftJsonMeta : Except String α → TranslateMetaM α
  | Except.ok value => pure value
  | Except.error err => failTranslateMeta err

def consLocal (fvar : Expr) (locals : Array Expr) : Array Expr :=
  #[fvar] ++ locals

partial def termToExprMeta (term : Json) (locals : Array Expr) : TranslateMetaM Expr := do
  let node ← liftJsonMeta <| stringField term "node"
  match node with
  | "type" =>
      let level ← liftJsonMeta <| natField term "level"
      pure <| cureSort level
  | "var" =>
      let index ← liftJsonMeta <| natField term "index"
      match locals[index]? with
      | some fvar => pure fvar
      | none => failTranslateMeta s!"unbound variable index in Lean backend: {index}"
  | "pi" =>
      let dom ← termToExprMeta (← liftJsonMeta <| jsonField term "dom") locals
      Meta.withLocalDecl Name.anonymous BinderInfo.default dom fun fvar => do
        let cod ← termToExprMeta (← liftJsonMeta <| jsonField term "cod") (consLocal fvar locals)
        Meta.mkForallFVars #[fvar] cod
  | "lam" =>
      let dom ← termToExprMeta (← liftJsonMeta <| jsonField term "dom") locals
      Meta.withLocalDecl Name.anonymous BinderInfo.default dom fun fvar => do
        let body ← termToExprMeta (← liftJsonMeta <| jsonField term "body") (consLocal fvar locals)
        Meta.mkLambdaFVars #[fvar] body
  | "app" =>
      let fnExpr ← termToExprMeta (← liftJsonMeta <| jsonField term "fun") locals
      let arg ← termToExprMeta (← liftJsonMeta <| jsonField term "arg") locals
      pure <| mkApp fnExpr arg
  | "global" =>
      let name ← liftJsonMeta <| stringField term "name"
      pure <| mkConst (cureName name)
  | "eq" =>
      let ty ← termToExprMeta (← liftJsonMeta <| jsonField term "type") locals
      let lhs ← termToExprMeta (← liftJsonMeta <| jsonField term "lhs") locals
      let rhs ← termToExprMeta (← liftJsonMeta <| jsonField term "rhs") locals
      Meta.mkAppOptM ``Eq #[some ty, some lhs, some rhs]
  | "refl" =>
      let value ← termToExprMeta (← liftJsonMeta <| jsonField term "value") locals
      Meta.mkAppOptM ``Eq.refl #[none, some value]
  | "rewrite" =>
      let proof ← termToExprMeta (← liftJsonMeta <| jsonField term "proof") locals
      let motive ← termToExprMeta (← liftJsonMeta <| jsonField term "motive") locals
      let body ← termToExprMeta (← liftJsonMeta <| jsonField term "body") locals
      Meta.mkAppOptM ``Eq.ndrec #[none, none, some motive, some body, none, some proof]
  | "sigma" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "pair" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "fst" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "snd" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "data" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "ctor" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "case" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "prim" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "int_type" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "int_lit" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "float_type" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | "float_lit" =>
      failTranslateMeta s!"unsupported Core node in Lean backend: {node}"
  | other =>
      failTranslateMeta s!"unknown Core node in Lean backend: {other}"

def termToExpr (term : Json) : TranslateM Expr := do
  let (result, _) ← Meta.MetaM.run <| (termToExprMeta term #[]).run
  match result with
  | Except.ok expr => pure expr
  | Except.error err => failTranslate err

def checkDef (defn : Json) : TranslateM Unit := do
  let nameString ← liftJson <| stringField defn "name"
  let typeJson ← liftJson <| jsonField defn "type"
  let bodyJson ← liftJson <| jsonField defn "body"
  let typeExpr ← termToExpr typeJson
  let bodyExpr ← termToExpr bodyJson

  let (_, _) ← Meta.MetaM.run do
    Meta.check typeExpr
    Meta.check bodyExpr
    let inferred ← Meta.inferType bodyExpr
    unless (← Meta.isDefEq inferred typeExpr) do
      throwError "definition body does not have its declared type"

  addDecl <| Declaration.defnDecl {
    name := cureName nameString,
    levelParams := [],
    type := typeExpr,
    value := bodyExpr,
    hints := ReducibilityHints.opaque,
    safety := DefinitionSafety.safe
  }

def checkDefs (defs : Array Json) : TranslateM Unit := do
  for defn in defs do
    checkDef defn

def checkModulePayload (payload : Json) : CoreM (Except String Unit) := do
  match stringField payload "format" with
  | Except.ok "cure-core-v1" =>
      match arrayField payload "defs" with
      | Except.ok defs => (checkDefs defs).run
      | Except.error err => pure <| Except.error err
  | Except.ok other =>
      pure <| Except.error s!"unsupported module format: {other}"
  | Except.error err =>
      pure <| Except.error err

def runCheckModule (payload : Json) : IO (Except String Unit) := do
  let env ← importModules #[{ module := `Init }] Options.empty
  let ctx : Core.Context := {
    fileName := "<cure-lean-bridge>",
    fileMap := FileMap.ofString ""
  }
  let state : Core.State := { env := env }
  let (result, _state) ← (checkModulePayload payload).toIO ctx state
  pure result

def handleHealth : IO Json := do
  let lean4leanPath := (← IO.getEnv "CURE_LEAN4LEAN_PATH").getD "../../lean4lean"
  let lean4leanAvailable ← System.FilePath.pathExists (System.FilePath.mk lean4leanPath)
  pure <| jsonOk [
    ("protocol", Json.num protocolVersion),
    ("lean_version", Json.str Lean.versionString),
    ("lean4lean_path", Json.str lean4leanPath),
    ("lean4lean_available", Json.bool lean4leanAvailable)
  ]

def handleCheckModule (request : Json) : IO Json := do
  match jsonField request "payload" with
  | Except.error err => pure <| jsonError err
  | Except.ok payload =>
      match (← runCheckModule payload) with
      | Except.ok () =>
          pure <| jsonOk [
            ("protocol", Json.num protocolVersion),
            ("checked_by", Json.str "lean")
          ]
      | Except.error err =>
          pure <| jsonDiagnostics <| Json.arr #[
            Json.mkObj [
              ("code", Json.str "lean_check_failed"),
              ("message", Json.str err)
            ]
          ]

def handleRequest (request : Json) : IO Json := do
  match getString? request "op" with
  | some "health" => handleHealth
  | some "check_module" => handleCheckModule request
  | some other => pure <| jsonError s!"unknown operation: {other}"
  | none => pure <| jsonError "missing operation"

def main : IO UInt32 := do
  let input ←
    match (← IO.getEnv "CURE_LEAN_BRIDGE_REQUEST") with
    | some request => pure request
    | none =>
        let stdin ← IO.getStdin
        stdin.readToEnd
  match Json.parse input with
  | Except.ok request =>
      let response ← handleRequest request
      IO.println response.compress
      pure 0
  | Except.error err =>
      IO.println (jsonError s!"invalid JSON: {err}").compress
      pure 1
