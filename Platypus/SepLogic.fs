module SepLogic

open Utils
open State

type VarName = Program.VarName

type TypedVar =
    | VarInt of VarName
    | VarAddr of VarName

    member self.Name
        with get () =
            match self with
            | VarInt name -> name
            | VarAddr name -> name

    override self.ToString() =
        match self with
        | VarInt name -> name
        | VarAddr name -> name

type PredicateName =
    | List
    | Tree

    override self.ToString() =
        match self with
        | List -> "ls"
        | Tree -> "tree"

    static member FromString n =
        match n with
        | "ls"
        | "list" -> List
        | "tree" -> Tree
        | _ -> failwith (sprintf "Unknown predicate name %s" n)

type RelationType =
    | Eq
    | Ne

    override self.ToString() =
        match self with
        | Eq -> "=="
        | Ne -> "<>"

/// Get a fresh variable of an unrestricted name.
let private FreshRandomAddrVar varCounter v =
    varCounter := !varCounter + 1
    VarAddr ("_" + v + string !varCounter)

// This is a hack, don't judge me.
// List.map is efficient and uses a an internal (mutation-based) hack to iterate only once.
// List.fold is as you would expect, and would thus traverse the list twice.
// So what this does is do a map, and keep the boolean flag in an extra mutable var which is manipulated on the way.
// Formally, it maps [x0, ..., xn] to [snd (f x0), ..., snd (f xn)] and also returns (fst (f x0)) || ... || (fst (f xn))
let private ListMapWithBoolFlag (f : 'T -> (bool * 'S)) (xs : 'T list) : (bool * 'S list) =
    let flag = ref false
    let xsMapped =
        List.map
            (fun x ->
                let (xFlag, xMapped) = f x
                flag := !flag || xFlag
                xMapped)
            xs
    (!flag, xsMapped)

// revmap from sequence to list, looping through a boolean flag
// Formally, it maps [x0, ..., xn] to [snd (f xn), ..., snd (f x0)])
let private MapToCollectionList (f : 'T -> (bool * 'S)) (flag : bool ref) (xs : 'T seq) : System.Collections.Generic.List<'S> =
    let res = System.Collections.Generic.List<'S>()
    for x in xs do
        let (xFlag, xMapped) = f x
        flag := !flag || xFlag
        res.Add xMapped
    res

type Expr =
    | Nil
    | Var of TypedVar
    override self.ToString () =
        match self with
        | Nil    -> "nil"
        | Var(VarInt n) -> n  //TODO separate these?
        | Var(VarAddr n) -> n

    member self.Variables
        with get () =
            match self with
            | Nil -> Set.empty
            | Var(v) -> Set.singleton v

    /// Takes a map { v1 -> t1, ..., vn -> tn }, returns (flag, expr) where expr is self with
    /// occurrences of v_i replaced by t_i, and flag true iff expr != self
    static member alpha (r : System.Collections.Generic.Dictionary<TypedVar,Expr>) self =
        match self with
        | Nil   -> (false, self)
        | Var n ->
            match r.TryGetValue n with
            | (true, newN) -> (true, newN)
            | (false, _)   -> (false, self)

    /// Instantiates "variable" by "expression" in "self". Returns pair (flag, expr), where flag is true iff "expr" is different from "self"
    static member instantiate variable expression self : (bool * Expr) =
        match self with
        | Var n when n = variable -> (true, expression)
        | _ -> (false, self)

[<StructuralEquality;StructuralComparison>]
///Note: This is immutable, and operations on it return a fresh clone.
type PureFormula =
    | Relation of RelationType * Expr * Expr
    override self.ToString () =
        match self with
        | Relation (relType, e1, e2) -> sprintf "%s %s %s" (e1.ToString()) (relType.ToString()) (e2.ToString())

    member self.Variables
        with get () =
            match self with
            | Relation (_, e1, e2) -> Set.union (e1.Variables) (e2.Variables)

    static member alpha (r : System.Collections.Generic.Dictionary<TypedVar,Expr>) self : (bool * PureFormula) =
        match self with
        | Relation (relType, e1, e2) ->
            let (e1IsChanged, e1Instantiated) = Expr.alpha r e1
            let (e2IsChanged, e2Instantiated) = Expr.alpha r e2
            if e1IsChanged || e2IsChanged then
                (true, Relation (relType, e1Instantiated, e2Instantiated))
            else
                (false, self)

///Spatial higher-order predicates. A higher order predicate has, additionally to normal parameters,
///another symbolic heap as parameter. This is used to further specify the value of existentially quantified variables.
///There is an interdependence between the free variables of the type parameter H and the expansion rules: The number
///of free variables H has to be equal to the number of parameters of the predicate plus the number of existentially
///quantified variables in expansion rules.
///Note: This is immutable, and operations on it return a fresh clone.
and [<AbstractClass>] SpatialFormula () =
    abstract Variables : Set<TypedVar> with get
and PointsTo (definedVariable : Expr, arguments : Expr list) =
    inherit SpatialFormula ()
    let mutable hashCodeCache = None
    member __.DefinedVariable with get () = definedVariable
    member __.Arguments       with get () = arguments

    override __.ToString () =
        let varList = arguments |> List.map (fun e -> e.ToString()) |> String.concat ", "
        sprintf "%s -> [%s]" (definedVariable.ToString()) varList

    override __.Variables with get () = Set.unionMany (definedVariable::arguments |> List.map (fun e -> e.Variables))

    static member private ProjectToTuple (pointsTo : PointsTo) =
        (pointsTo.DefinedVariable, pointsTo.Arguments)
    override self.GetHashCode () =
        match hashCodeCache with
        | Some h -> h
        | None ->
            let hashCode = hashOn PointsTo.ProjectToTuple self
            hashCodeCache <- Some hashCode
            hashCode
    override self.Equals o =
        equalsOn PointsTo.ProjectToTuple self o

    static member alpha (r : System.Collections.Generic.Dictionary<TypedVar,Expr>) (self : PointsTo) =
        let (defVarChanged, defVarInstantiated) = Expr.alpha r self.DefinedVariable
        let (argsChanged, argsInstantiated) = ListMapWithBoolFlag (Expr.alpha r) self.Arguments
        if defVarChanged || argsChanged then
            (true, PointsTo (defVarInstantiated, argsInstantiated))
        else
            (false, self)

and Predicate (predicateName : PredicateName, typeParameter : SymHeap option, arguments : Expr list) =
    inherit SpatialFormula ()
    let mutable hashCodeCache = None
    member __.PredicateName with get () = predicateName
    member __.TypeParameter with get () = typeParameter
    member __.Arguments     with get () = arguments

    override __.ToString () =
        let varList = arguments |> List.map (fun e -> e.ToString()) |> String.concat ", "
        let typeParString =
            match typeParameter with
            | Some typeParVal -> sprintf "\\ %s" (typeParVal.ToString())
            | None            -> "None"
        sprintf "%s(%s | %s)" (predicateName.ToString()) varList typeParString

    override __.Variables with get () = Set.unionMany (arguments |> List.map (fun e -> e.Variables))

    static member private projectToTuple (predicate: Predicate) =
        (predicate.PredicateName, predicate.TypeParameter, predicate.Arguments)
    override self.GetHashCode () =
        match hashCodeCache with
        | Some h -> h
        | None ->
            let hashCode = hashOn Predicate.projectToTuple self
            hashCodeCache <- Some hashCode
            hashCode
    override self.Equals o =
        equalsOn Predicate.projectToTuple self o

    static member alpha (r : System.Collections.Generic.Dictionary<TypedVar,Expr>) (self : Predicate) =
        let (typeParChanged, typeParInstantiated) =
            match self.TypeParameter with
            | None ->
                (false, None)
            | Some typePar ->
                //remove shadowed mappings from r:
                let r = System.Collections.Generic.Dictionary(r)
                typePar.AllVars |> Seq.iter (fun v -> r.Remove v |> ignore)
                //only continue if variable isn't shadowed:
                let (typeParChanged, typeParInstantiated) = SymHeap.alpha r typePar
                (typeParChanged, Some typeParInstantiated)
        let (argsChanged, argsInstantiated) = ListMapWithBoolFlag (Expr.alpha r) self.Arguments

        if typeParChanged || argsChanged then
            (true, Predicate (self.PredicateName, typeParInstantiated, argsInstantiated))
        else
            (false, self)

/// Note: This is not immutable, and operations will change existing copy. If you want to avoid this, use .Clone()
and SymHeap () =
    let mutable freeVars : System.Collections.Generic.List<TypedVar> = System.Collections.Generic.List()
    let mutable exVars : System.Collections.Generic.List<TypedVar> = System.Collections.Generic.List()
    let mutable pureFormulas = System.Collections.Generic.List()
    let mutable predicates = System.Collections.Generic.List()
    let mutable pointsTos = System.Collections.Generic.List()

    let mutable defHeapletCache = null
    let mutable reachableCache : System.Collections.Generic.HashSet<TypedVar> = null
    let mutable hashCodeCache = None
    let mutable variableEqualityMappings = Map.empty
    let mutable level = 0

    member __.FreeVars
        with         get () = freeVars
        and private  set v  = freeVars <- v
    member __.ExVars
        with         get () = exVars
        and private  set v  = exVars <- v
    member __.PureFormulas
        with         get () = pureFormulas
        and private  set v  = pureFormulas <- v
    member __.Predicates
        with         get () = predicates
        and private  set v  = predicates <- v
    member __.PointsTos
        with         get () = pointsTos
        and private  set v  = pointsTos <- v
    member __.DefiningHeapletCache
        with private get () = defHeapletCache
        and private  set v  = defHeapletCache <- v
    member __.ReachableCache
        with private get () = reachableCache
        and private  set v  = reachableCache <- v
    member __.HashCodeCache
        with private get () = hashCodeCache
        and private  set v  = hashCodeCache <- v
    member __.VariableEqualityMappings
        with         get () = variableEqualityMappings
        and          set v  = variableEqualityMappings <- v
    member __.Level
        with         get () = level
        and          set v  = level <- v

    /// (Deep) copy:
    member self.Clone () =
        new SymHeap(FreeVars = System.Collections.Generic.List (self.FreeVars),
                    ExVars = System.Collections.Generic.List (self.ExVars),
                    PureFormulas = System.Collections.Generic.List (self.PureFormulas),
                    Predicates = System.Collections.Generic.List (self.Predicates),
                    PointsTos = System.Collections.Generic.List (self.PointsTos),
                    VariableEqualityMappings = self.VariableEqualityMappings,
                    Level = self.Level)

    /// Renaming, giving you a deep copy when changed, or just itself when there is no change
    static member alpha (r : System.Collections.Generic.Dictionary<TypedVar,Expr>) (self : SymHeap) =
        //For a variable renaming, track this in free/existentials. For anything else, drop the variable:
        let changed = ref false
        let renameVar v =
            match r.TryGetValue v with
            | (true, Var v') when v <> v' ->
                changed := !changed || true
                v'
            | _ -> v
        let newFreeVars = System.Collections.Generic.List(Seq.map renameVar self.FreeVars)
        let newExVars = System.Collections.Generic.List(Seq.map renameVar self.ExVars)
        let newPureFormulas = MapToCollectionList (PureFormula.alpha r) changed self.PureFormulas
        let newPointsTos = MapToCollectionList (PointsTo.alpha r) changed self.PointsTos
        let newPredicates = MapToCollectionList (Predicate.alpha r) changed self.Predicates

        if !changed then
            let newSymHeap =
                new SymHeap(
                    FreeVars = newFreeVars,
                    ExVars = newExVars,
                    PureFormulas = newPureFormulas,
                    PointsTos = newPointsTos,
                    Predicates = newPredicates,
                    VariableEqualityMappings = self.VariableEqualityMappings,
                    Level = self.Level)
            (true, newSymHeap)
        else
            (false, self)
    member self.Rename (r : System.Collections.Generic.Dictionary<TypedVar, Expr>) =
        snd (SymHeap.alpha r self)

    member private self.MutatingAlpha (r : System.Collections.Generic.Dictionary<TypedVar,Expr>) =
        self.ExVars.RemoveAll(System.Predicate(fun v -> r.ContainsKey v)) |> ignore
        let flag = ref false
        self.PureFormulas <- MapToCollectionList (PureFormula.alpha r) flag self.PureFormulas
        self.Predicates <- MapToCollectionList (Predicate.alpha r) flag self.Predicates
        self.PointsTos <- MapToCollectionList (PointsTo.alpha r) flag self.PointsTos
        if reachableCache <> null then
            reachableCache.RemoveWhere(System.Predicate(fun v -> r.ContainsKey v)) |> ignore
        self.HashCodeCache <- None
        if !flag then
            self.DefiningHeapletCache <- null

    /// Creates a new symbolic heap by removing the given heaplet and instead adding the given new spatial and pure formulas and existential variables.
    member self.ResetPredicates (newPredicates : Predicate seq) =
        let newState = self.Clone ()
        newState.Predicates <- System.Collections.Generic.List newPredicates
        //TODO: We can and should do better:
        newState.DefiningHeapletCache <- null
        newState.ReachableCache <- null
        newState

    /// Create a new symbolic heap that contains additional information.
    member self.CreateExtension newPredicates newPointsTo newPure newExistentials =
        let newState = self.Clone ()
        newState.Predicates.AddAll newPredicates
        newState.PointsTos.AddAll newPointsTo
        newState.PureFormulas.AddAll newPure
        newState.ExVars.AddAll newExistentials
        //TODO: We can and should do better:
        newState.DefiningHeapletCache <- null
        newState.ReachableCache <- null
        newState

    member self.AddPure newPure =
        self.PureFormulas.AddAll newPure

    /// Constructor for F# uses:
    static member ofSeqs
        (freeVars : TypedVar seq)
        (exVars : TypedVar seq)
        (pureFormulas : PureFormula seq)
        (predicates : Predicate seq)
        (pointsTo : PointsTo seq) =
        new SymHeap(FreeVars = System.Collections.Generic.List freeVars,
                    ExVars = System.Collections.Generic.List exVars,
                    PureFormulas = System.Collections.Generic.List pureFormulas,
                    Predicates = System.Collections.Generic.List predicates,
                    PointsTos = System.Collections.Generic.List pointsTo)

    override self.ToString () =
        let pureAtoms =
            self.VariableEqualityMappings 
            |> Seq.map (function KeyValue(k,v) -> sprintf "%s %s %s" (k.ToString()) (Eq.ToString()) (v.ToString()))
        let pureAtoms = Seq.append pureAtoms (self.PureFormulas |> Seq.map (fun f -> f.ToString()))
        let pureF =
            if Seq.isEmpty pureAtoms then
                "true"
            else
                pureAtoms |> String.concat " && "
        let spatialString =
            if self.Predicates.Count + self.PointsTos.Count = 0 then
                "emp"
            else
                let predicateStrings = self.Predicates |> Seq.map (fun p -> p.ToString())
                let pointsToStrings = self.PointsTos |> Seq.map (fun p -> p.ToString())
                Seq.append predicateStrings pointsToStrings |> String.concat " * "
        let freeVarString = self.FreeVars |> Seq.map (fun v -> v.ToString ()) |> String.concat ", "
        if self.ExVars.Count = 0 then
            sprintf "(%s) -> %s : %s" freeVarString pureF spatialString
        else
            let exVarList = self.ExVars |> Seq.map (fun v -> v.ToString ()) |> String.concat ", "
            sprintf "(%s) -> Ex. %s . %s : %s" freeVarString exVarList pureF spatialString

    override self.Equals other =
        match other with
        | :? SymHeap as otherHeap ->
            (    (System.Linq.Enumerable.SequenceEqual (otherHeap.FreeVars, self.FreeVars))
              && (System.Linq.Enumerable.SequenceEqual (otherHeap.ExVars, self.ExVars))
              && (System.Linq.Enumerable.SequenceEqual (otherHeap.PureFormulas, self.PureFormulas))
              && (System.Linq.Enumerable.SequenceEqual (otherHeap.Predicates, self.Predicates))
              && (System.Linq.Enumerable.SequenceEqual (otherHeap.PointsTos, self.PointsTos)))
        | _ -> false
    override self.GetHashCode () =
        if hashCodeCache.IsNone then
            hashCodeCache <-
                Some (3 + Seq.fold (fun s (v : TypedVar) -> s + 5 * v.GetHashCode()) 0 self.FreeVars
                        + Seq.fold (fun s (v : TypedVar) -> s + 7 * v.GetHashCode()) 0 self.ExVars
                        + Seq.fold (fun s (f : PureFormula) -> s + 11 * f.GetHashCode()) 0 self.PureFormulas
                        + Seq.fold (fun s (p : PointsTo) -> s + 13 * p.GetHashCode()) 0 self.PointsTos
                        + Seq.fold (fun s (f : Predicate) -> s + 17 * f.GetHashCode()) 0 self.Predicates)
        hashCodeCache.Value
    member self.AllVars 
        with get () =
            Seq.append self.FreeVars self.ExVars

    member self.IsPredless with get () = self.Predicates.Count = 0

    member private self.FillDefHeapletCache () =
        if self.DefiningHeapletCache = null then
            self.DefiningHeapletCache <- System.Collections.Generic.Dictionary()
            for predicate in self.Predicates do
                match predicate.Arguments with
                | Var(v) :: _ -> self.DefiningHeapletCache.[v] <- (predicate :> SpatialFormula)
                | _ -> ()
            for pointsTo in self.PointsTos do
                match pointsTo.DefinedVariable with
                | Var v -> self.DefiningHeapletCache.[v] <- (pointsTo :> SpatialFormula)
                | _ -> ()

    member self.IsUndefinedVariable
        with get (var : TypedVar) : bool =
            self.FillDefHeapletCache ()
            let defHeaplet : SpatialFormula option = self.TryFindDefiningHeaplet var
            defHeaplet.IsNone

    member private self.ComputeReachables () =
        if reachableCache = null then
            reachableCache <- System.Collections.Generic.HashSet()

            let directlyReachable = ListDictionary()
            for predicate in self.Predicates do
                match predicate.Arguments with
                | ((Var v) :: arguments) ->
                    directlyReachable.[v] <- arguments |> List.collect (function | Var(v) -> [v] | _ -> [])
                | _ -> ()
            for pointsTo in self.PointsTos do
                match pointsTo.DefinedVariable with
                | Var v ->
                    directlyReachable.[v] <- pointsTo.Arguments |> List.collect (function | Var(v) -> [v] | _ -> [])
                | _ -> ()

            let mutable stack = List.ofSeq self.FreeVars
            while not(List.isEmpty stack) do
                let v = List.head stack
                stack <- List.tail stack
                if reachableCache.Add v then
                    stack <- directlyReachable.[v] @ stack

    member self.TryFindDefiningHeaplet x =
        self.FillDefHeapletCache ()
        match self.DefiningHeapletCache.TryGetValue x with
        | (true, res) -> Some res
        | (false, _)  -> None

    member private self.Reachable
        with get () =
            self.ComputeReachables ()
            reachableCache

    member self.Simplify () =
        let reachableVars = self.Reachable
        let unneededPF =
            function
                | Relation(Eq, v1, v2) when v1 = v2 -> true
                | Relation(_, Var(v1), Var(v2)) when not(reachableVars.Contains v1) || not(reachableVars.Contains v2) ->
                    true
                | _ -> false
        let unneededPredicate (predicate : Predicate) =
            match predicate.Arguments with
            | Var(v)::_ -> not(reachableVars.Contains v)
            | _ -> false
        let unneededPointsTo (pointsTo : PointsTo) =
            match pointsTo.DefinedVariable with
            | Var v -> not(reachableVars.Contains v)
            | _ -> false
        self.PureFormulas.RemoveAll(System.Predicate(unneededPF)) |> ignore
        self.Predicates.RemoveAll(System.Predicate(unneededPredicate)) |> ignore
        self.PointsTos.RemoveAll(System.Predicate(unneededPointsTo)) |> ignore
        self.ExVars.RemoveAll(System.Predicate(fun v -> not (reachableVars.Contains v))) |> ignore
        self.HashCodeCache <- None

    static member standardize (s : SymHeap) =
        s.Simplify ()
        let standardArgNames = System.Collections.Generic.Dictionary()
        let mutable argCount = 0
        for v in s.FreeVars do
            if not(standardArgNames.ContainsKey v) then
                match v with
                | VarInt _ ->
                    standardArgNames.[v] <- Var (VarInt (sprintf "arg%i" argCount))
                | VarAddr _ ->
                    standardArgNames.[v] <- Var (VarAddr (sprintf "arg%i" argCount))
                argCount <- argCount + 1
        let renamedState = s.Rename standardArgNames //this implicitly clones the state (iff renaming changes anything)
        ///Take care of duplicates:
        renamedState.PureFormulas <- System.Collections.Generic.List (System.Collections.Generic.HashSet renamedState.PureFormulas)
        renamedState.Predicates <- System.Collections.Generic.List (System.Collections.Generic.HashSet renamedState.Predicates)
        renamedState.PointsTos <- System.Collections.Generic.List (System.Collections.Generic.HashSet renamedState.PointsTos)
        renamedState

    member self.IsContradictory
        with get () =
            let directContradiction () =
                self.PureFormulas |> Seq.exists (function | Relation(Ne, Var v, Var v') when v = v' -> true
                                                          | Relation(Ne, Nil, Nil) -> true | _ -> false)
            let nilDefinedInPointsTo () =
                self.PointsTos |> Seq.exists (fun p -> Nil = p.DefinedVariable)
            let nilDefinedInPredicate () =
                self.Predicates |> Seq.exists (fun p -> Nil = List.head p.Arguments)
            let higherOrderContradiction () =
                self.Predicates |> Seq.exists (fun p -> match p.TypeParameter with | Some s -> s.IsContradictory | _ -> false)
            (nilDefinedInPointsTo ()) || (nilDefinedInPredicate ()) || (directContradiction ()) || (higherOrderContradiction ())

    member self.SetUndefinedToNil () =
        let reachables = System.Collections.Generic.List (self.Reachable)
        let nilSubstitution = System.Collections.Generic.Dictionary ()
        for v in reachables do
            if (self.TryFindDefiningHeaplet v).IsNone && not (self.VariableEqualityMappings.ContainsKey v) then
                self.VariableEqualityMappings <- Map.add v Nil self.VariableEqualityMappings
                nilSubstitution.[v] <- Nil
        if nilSubstitution.Count > 0 then
            self.MutatingAlpha nilSubstitution

    /// Resolves equalities var = expr by replacing all occurrences of var by expr.
    member self.ResolveEqualities () =
        //To reduce the number of (expensive) alphas on the full state, we build the transitive
        //closure of equalities here before dispatching this as renaming of the state
        let equalityPairs = ref []
        let updateEqualityMap v e =
            let mutable e = e
            let mutable newMapping = []
            for (v', e') in !equalityPairs do
                e <- snd (Expr.instantiate v' e' e)
            for (v', e') in !equalityPairs do
                newMapping <- (v', snd (Expr.instantiate v e e')) :: newMapping
            self.VariableEqualityMappings <- Map.add v e self.VariableEqualityMappings
            equalityPairs := (v, e) :: newMapping
        for pureF in System.Collections.Generic.List self.PureFormulas do
            match pureF with
            | Relation (Eq, e1, e2) when e1 = e2 ->
                self.PureFormulas.Remove pureF |> ignore
            | Relation (Eq, Var v1, Var v2) ->
                match self.TryFindDefiningHeaplet v1 with
                | Some _ -> updateEqualityMap v2 (Var v1)
                | None   -> updateEqualityMap v1 (Var v2)
            | Relation (Eq, Var v, e)
            | Relation (Eq, e, Var v) ->
                updateEqualityMap v e
            | _ -> ()
        if not(List.isEmpty !equalityPairs) then
            let equalityMap = System.Collections.Generic.Dictionary()
            !equalityPairs |> List.iter (fun (v, e) -> equalityMap.[v] <- e)
            self.MutatingAlpha equalityMap

type ExpRule =
    {
        /// The parameters of the predicate. By convention, the first one is the start of the defined data structure.
        Parameters : TypedVar list;

        /// Possible expansions of the predicate. "Free" variables correspond to the parameters,
        /// and existential variables are those that are additionally named in the expansion step.
        /// A rule
        ///    pred -> \lambda F1 ... FN . Ex. E1 ... EM . \phi : \psi
        /// is applied on pred(\tau, a1...an) in a heap H by removing that heaplet, renaming E1 ... EM
        /// to be unique in H, and replacing occurrences of F1 ... FN by a1 ... an. Additionally,
        /// \tau is instantiated with a1, ..., an, E1, ..., EM and added to the heap.
        Expansions : (SymHeap * bool) list;

        /// List indicating the number of parameters of a possibly nested symbolic heap,
        /// as a boolean flag indicating which variables can in turn contain nested data structures.
        /// By convention, this should correspond to the list of predicate parameters and the (maximal)
        /// list of existentials
        HigherOrderParameters : bool list;
    }

let expansionRules predicate =
    match predicate with
    | List ->
        {
            Parameters = [VarAddr "x"; VarAddr "y"];
            HigherOrderParameters = [ false ; false ; true ; false ];
            Expansions =
                [
                      ( SymHeap.ofSeqs [ VarAddr "x" ; (VarAddr "y")]
                                       []
                                       [ Relation (Eq, Var (VarAddr "x"), Var (VarAddr "y")) ]
                                       []
                                       []
                      , false)
                    ; ( SymHeap.ofSeqs [ VarAddr "x" ; (VarAddr "y")]
                                       [ VarInt "v" ; VarAddr "z"]
                                       []
                                       [ Predicate (List, None, [Var (VarAddr "z"); Var (VarAddr "y")]) ]
                                       [ PointsTo (Var (VarAddr "x"), [Var (VarInt "v"); Var (VarAddr "z")]) ]
                      , true)
                ]
        }

    | Tree ->
       {
            Parameters = [VarAddr "x"];
            HigherOrderParameters = [ false ; true ; false ; false ];
            Expansions =
                [
                      ( SymHeap.ofSeqs [ VarAddr "x" ]
                                       [ (VarInt "v") ; (VarAddr "l") ; (VarAddr "r") ]
                                       []
                                       [ Predicate(Tree, None, [Var (VarAddr "l") ])
                                       ; Predicate(Tree, None, [Var (VarAddr "r") ]) ]
                                       [ PointsTo(Var (VarAddr "x"), [Var (VarInt "v") ; Var (VarAddr "l") ; Var (VarAddr "r")]) ]
                      , true)
                    ; ( SymHeap.ofSeqs [ VarAddr "x" ]
                                       [ (VarInt "v") ; (VarAddr "l") ]
                                       []
                                       [ Predicate(Tree, None, [Var (VarAddr "l") ]) ]
                                       [ PointsTo(Var (VarAddr "x"), [Var (VarInt "v") ; Var (VarAddr "l") ; Nil]) ]
                      , true)
                    ; ( SymHeap.ofSeqs [ VarAddr "x" ]
                                       [ (VarInt "v") ; (VarAddr "r") ]
                                       []
                                       [ Predicate(Tree, None, [Var (VarAddr "r") ]) ]
                                       [ PointsTo(Var (VarAddr "x"), [Var (VarInt "v") ; Nil ; Var (VarAddr "r")]) ]
                      , true)
                    ; ( SymHeap.ofSeqs [ VarAddr "x" ]
                                       [ (VarInt "v") ; ]
                                       []
                                       []
                                       [ PointsTo(Var (VarAddr "x"), [Var (VarInt "v") ; Nil ; Nil]) ]
                      , true)
                ]
        }


let PerformRuleExpansion varCounter higherOrderParameters (arguments : Expr list) (typeParameter : SymHeap option) ((heapToAdd, hasNesting) : (SymHeap * bool)) =
    // Step 1: Get fresh names for everything, create a renaming map:
    let varInstantiation = System.Collections.Generic.Dictionary()
    for (parameter, argument) in Seq.zip heapToAdd.FreeVars arguments do
        varInstantiation.[parameter] <- argument
    let exVarRenaming = System.Collections.Generic.Dictionary()
    for exVar in heapToAdd.ExVars do
        let freshExVar = FreshRandomAddrVar varCounter "ev"
        varInstantiation.[exVar] <- Var freshExVar
        exVarRenaming.[exVar] <- freshExVar

    // Step 2: Prepare all the bits that we want to add. This includes instantiating the type parameter, if there is one.
    let (predicatesToAdd, pointsTosToAdd, pureAtomsToAdd, exVarsToAdd) : (Predicate seq * PointsTo seq * PureFormula seq * TypedVar seq) =
        match (hasNesting, typeParameter) with
        | (true, Some typePar) ->
            let arguments = Seq.append arguments (heapToAdd.ExVars |> Seq.map (fun n -> varInstantiation.[n]))
            let typeParInstantiation = System.Collections.Generic.Dictionary()
            for (typeParPar, typeParArg) in Seq.zip typePar.FreeVars arguments do
                typeParInstantiation.[typeParPar] <- typeParArg
            for typeParExVar in typePar.ExVars do
                typeParInstantiation.[typeParExVar] <- Var (FreshRandomAddrVar varCounter "nv")
            let instantiatedTypePar = (typePar.Clone()).Rename typeParInstantiation
            (instantiatedTypePar.Predicates :> _,
             instantiatedTypePar.PointsTos :> _,
             instantiatedTypePar.PureFormulas :> _,
             instantiatedTypePar.ExVars :> _)
        | _ -> (Seq.empty, Seq.empty, Seq.empty, Seq.empty)

    // Get the names of the variables that are starting the new subheap
    // (i.e., the parameters of the nested heap that are nestable, renamed).
    // We use that only exVars can be nestable (that allows us to avoid unpacking a Var (...))
    let startOfSubheapVariables =
        Seq.zip heapToAdd.AllVars higherOrderParameters |> Seq.filter snd |> Seq.map (fun (v, _) -> exVarRenaming.[v])
    let newSubheapStarts = (startOfSubheapVariables, exVarsToAdd)

    let newPredicatesWithInstantiatedParameters =
        heapToAdd.Predicates
        |> Seq.map (fun predicate -> Predicate(predicate.PredicateName, typeParameter, predicate.Arguments))
        |> Seq.cache
    let newPredicateAtoms =
        Seq.append predicatesToAdd newPredicatesWithInstantiatedParameters
        |> Seq.map (Predicate.alpha varInstantiation >> snd)
        |> Seq.cache
    let newPointsToAtoms =
        Seq.append heapToAdd.PointsTos pointsTosToAdd
        |> Seq.map (PointsTo.alpha varInstantiation >> snd)
        |> Seq.cache
    let newPureAtoms =
        Seq.append pureAtomsToAdd heapToAdd.PureFormulas
        |> Seq.map (PureFormula.alpha varInstantiation >> snd)
        |> Seq.cache
    let newExVars =
        Seq.append (Seq.map (fun v -> exVarRenaming.[v]) heapToAdd.ExVars) exVarsToAdd
        |> Seq.cache

    (newPredicateAtoms, newPointsToAtoms, newPureAtoms, newExVars, newSubheapStarts)

///Do parallel expansion of all predicates in a state, and then build a set of new states from the cartesian product of results.
///This corresponds to BFS over the tree of expansions, and guarantees that predicates are expanded "evenly".
let private PredicateExpansion ((state, startOfSubheapToExistentials) : SymHeap * ListDictionary<TypedVar,TypedVar>) varCounter =
    let expandAllPredicates (predicates : Predicate seq) =
        let expandOnePredicate (predicate : Predicate) =
            let definedVal = List.head predicate.Arguments
            match definedVal with
            | Nil -> [ (Seq.empty, Seq.empty, Seq.empty, Seq.empty, (Seq.empty, Seq.empty)) ]
            | Var(_) ->
                //get expansion rules:
                let rules = expansionRules predicate.PredicateName
                List.map (PerformRuleExpansion varCounter rules.HigherOrderParameters predicate.Arguments predicate.TypeParameter) rules.Expansions
        Seq.map expandOnePredicate predicates

    let stateFromPredicateExpansionCombination (oldState : SymHeap) expansionsCombination =
        let (newPredicates, additionalPointsTo, additionalPureFormulas, additionalExVars, newSubheapStartInfos) =
            List.fold
                (fun (newPreds, addPoints, addPure, addEx, newSHI) (preds, points, pureF, ex, shi) ->
                    (Seq.append preds newPreds, Seq.append points addPoints, Seq.append pureF addPure, Seq.append ex addEx, shi :: newSHI))
                (Seq.empty, Seq.empty, Seq.empty, Seq.empty, [])
                expansionsCombination
        let newState =
            SymHeap.ofSeqs
                oldState.FreeVars
                (Seq.append oldState.ExVars additionalExVars)
                (Seq.append oldState.PureFormulas additionalPureFormulas)
                newPredicates
                (Seq.append oldState.PointsTos additionalPointsTo)
        newState.VariableEqualityMappings <- oldState.VariableEqualityMappings
        let extendedStartOfSubheapToExistentialVars = ListDictionary(startOfSubheapToExistentials)
        for (startOfSubheapVariables, exVarsToAdd) in newSubheapStartInfos do
            for v in startOfSubheapVariables do
                extendedStartOfSubheapToExistentialVars.AddMany (v, List.ofSeq exVarsToAdd)

        (newState, extendedStartOfSubheapToExistentialVars)

    state.Predicates
    |> expandAllPredicates
    |> List.ofSeq
    |> Utils.cartesianProduct
    |> List.map (stateFromPredicateExpansionCombination state)

let rec Expand varCounter (state : SymHeap * ListDictionary<TypedVar, TypedVar>) =
    //printfn "Expanding state %s" ((fst state).ToString())
    [
        let newLevel = (fst state).Level + 1
        for (expandedState, startOfSubheapToExistentialVars) in PredicateExpansion state varCounter do
            //printfn "  RawPredExp: %s" (expandedState.ToString())
            expandedState.ResolveEqualities () //this might make new contradictions pop up
            if not expandedState.IsContradictory then
                //printfn "  Eq'ed:      %s" (expandedState.ToString())
                let expandedState = SymHeap.standardize expandedState //This may not be done before the contradiction check, as it removes contradictory things...
                expandedState.SetUndefinedToNil ()
                if not expandedState.IsContradictory then
                    //printfn "  Filter1Exp: %s" (expandedState.ToString());
                    expandedState.Level <- newLevel
                    yield (expandedState, startOfSubheapToExistentialVars)
    ]

let private Instantiate (symState : SymHeap) (stackVars : TypedVar seq) (interestingExVars : TypedVar seq) (subheapStartToExVars : ListDictionary<TypedVar, TypedVar>) =
    //printfn "Instantiating %s" (symState.ToString())
    assert symState.IsPredless

    let state = State.empty (Seq.map (fun (v: TypedVar) -> v.Name) stackVars |> Set.ofSeq)
    let mutable nextVal = (bigint(1))
    let mutable varToValAddr = Map.empty
    let mutable varToAddrs = SetMap<TypedVar, bigint>.empty
    for var in symState.AllVars do
        match symState.TryFindDefiningHeaplet var with
        | Some spatialFormula ->
            match spatialFormula with
            | :? PointsTo as pointsTo ->
                let args = pointsTo.Arguments
                let mutable addr = nextVal
                varToValAddr <- Map.add var addr varToValAddr
                nextVal <- nextVal + bigint(args.Length) + bigint(1)

                for arg in args do
                    match arg with
                        | Var(v) ->
                            varToAddrs <- SetMap.add v addr varToAddrs
                        | Nil ->
                            state.heap.set addr (State.ValAddr bigint.Zero)
                    addr <- addr + bigint(1)
            | _ ->
                varToValAddr <- Map.add var bigint.Zero varToValAddr
        | _ ->
            if not (symState.VariableEqualityMappings.ContainsKey var) then
                varToValAddr <- Map.add var bigint.Zero varToValAddr

    let varToValAddr = varToValAddr //rebind to make non-mutable and usable in closure
    let rec getValueAddr expr =
        match expr with
        | Var v ->
            match symState.VariableEqualityMappings.TryFind v with
            | Some e when (Var v) <> e -> getValueAddr e
            | _ -> Map.FindWithDefault v bigint.Zero varToValAddr
        | Nil -> bigint.Zero

    //Now all variables should have values, fill the heap:
    for var in symState.AllVars do
        match var with
        | VarAddr _ ->
            let varValAddr = getValueAddr (Var var)
            if SetMap.containsKey var varToAddrs then
                for addr in varToAddrs.[var] do
                    state.heap.set addr (ValAddr varValAddr)
        | _ -> ()

    //Finally, set the stack variables (use original state to get this)
    for (stackVar, symVar) in (Seq.zip stackVars symState.FreeVars) do
        match stackVar with
        | VarAddr _ ->
            state.varStack.Set stackVar.Name (ValAddr (getValueAddr (Var symVar)))
        | VarInt _ ->
            state.varStack.Set stackVar.Name (ValInt bigint.Zero) //TODO: If we want to do int values, get model for pure formula and fill them in here

    //Also get values for those existential variables we care about:
    let subheapStartToExVarsForAddrs = ListDictionary<Addr, Addr>()
    for (var, exVars) in subheapStartToExVars do
        subheapStartToExVarsForAddrs.AddMany (getValueAddr (Var var), (List.map (fun v -> getValueAddr (Var v)) exVars))
    let overallExToAddr : Map<TypedVar, Addr> = interestingExVars |> Seq.map (fun v -> (v, getValueAddr (Var v))) |> Map.ofSeq

    (state, (overallExToAddr, subheapStartToExVarsForAddrs))

type private InitialDefiningHeaplets =
    {
        ParameterVariables : TypedVar list
        ExistentialVariables : TypedVar list
        InitialPureFormula : PureFormula list
        InitialPredicates : Predicate list
    }
let private InitialDefinitions =
    [
        // List from x to y
        {
            ParameterVariables    = [ (VarAddr "x") ; (VarAddr "y") ]
            ExistentialVariables  = [ ]
            InitialPureFormula    = [ ]
            InitialPredicates     = [ Predicate(List, None, [Var (VarAddr "x") ; Var (VarAddr "y")]) ]
        }

        // Cyclic list from x
    ;   {
            ParameterVariables    = [ (VarAddr "x") ]
            ExistentialVariables  = [ ]
            InitialPureFormula    = [  ]
            InitialPredicates     = [ Predicate(List, None, [Var (VarAddr "x") ; Var (VarAddr "x")]) ]
        }

        // Panhandle list from x
    ;   {
            ParameterVariables    = [ (VarAddr "x") ]
            ExistentialVariables  = [ (VarAddr "t") ]
            InitialPureFormula    = [ Relation(Ne, Var (VarAddr "x"), Nil) ; Relation(Ne, Var (VarAddr "x"), Var (VarAddr "t")) ;Relation(Ne, Var (VarAddr "t"), Nil) ]
            InitialPredicates     = [ Predicate(List, None, [Var (VarAddr "x") ; Var (VarAddr "t")])
                                    ; Predicate(List, None, [Var (VarAddr "t") ; Var (VarAddr "t")]) ]
        }

        // Tree from x
    ;   {
            ParameterVariables    = [ (VarAddr "x") ]
            ExistentialVariables  = [ ]
            InitialPureFormula    = [ Relation(Ne, Var (VarAddr "x"), Nil) ]
            InitialPredicates     = [ Predicate(Tree, None, [Var (VarAddr "x")]) ]
        }
    ]


/// toDefineVars are variables that will be instantiated (i.e., get a defining predicate),
/// freeVars are variables that are free variables of the generated heap
/// allKnownVars is a superset of the first two, maybe adding additional variables (to be treated as constants)
let private GuessFlatSymHeaps (toDefineVars: TypedVar list) (freeVars: TypedVar list) (allKnownVars: TypedVar list) needsNil noNilInNested varCounter =
    (*
     For every var, we choose an initial heaplet (or none, hence ignoring all
     information), and fill its remaining parameters with all permutations of
     variables.
     We also add a special variable "nilV" that we introduce to keep track
     of things that end in the nil value.
    *)
    let nilVar = VarAddr "nilV"
    let mutable res = [ SymHeap.ofSeqs freeVars (if needsNil then [nilVar] else []) [Relation (Eq, Var nilVar, Nil)] [] [] ]

    for var in toDefineVars do
        //Case 1: No definition for var, so we can just reuse our earlier results where it has no assigned type
        let mutable newRes = res |> List.filter (fun (partState : SymHeap) -> (partState.TryFindDefiningHeaplet var).IsNone)
        let defVarIsNonNil = Relation (Ne, Var var, Var nilVar)

        //Case 2: Choose an initial heaplet, instantiate it correctly
        for initialDefinition in InitialDefinitions do
            //Choose instantiation of the remaining parameters:
            let remainingParameters = List.tail initialDefinition.ParameterVariables
            let parameterInstantions =
                   allTuples remainingParameters.Length (nilVar :: allKnownVars)
                |> List.map (fun i -> var::i)
            for parameterInstance in parameterInstantions do
                let paramInstantiation = System.Collections.Generic.Dictionary()
                List.iter2 (fun var expr -> paramInstantiation.[var] <- Var expr) initialDefinition.ParameterVariables parameterInstance

                for partState in res do
                    // Step 2: Get already used variables rename the fresh existential variables appropriately
                    let usedVariables = System.Collections.Generic.HashSet(partState.AllVars)
                    usedVariables.AddAll allKnownVars
                    let initDefRenaming = System.Collections.Generic.Dictionary(paramInstantiation)
                    let newExistentials = ref []
                    List.iter (fun v ->
                                let newExistential = FreshRandomAddrVar varCounter "ini_ev"
                                initDefRenaming.[v] <- Var newExistential
                                newExistentials := newExistential :: !newExistentials)
                        initialDefinition.ExistentialVariables

                    // Step 3: Instantiate / rename the partial formula:
                    let renamedInitialPureFormula = initialDefinition.InitialPureFormula |> List.map (PureFormula.alpha initDefRenaming >> snd)
                    let renamedInitialPredicates = initialDefinition.InitialPredicates |> List.map (Predicate.alpha initDefRenaming >> snd)
                    let renamedInitialPureFormula =
                        if noNilInNested then
                            defVarIsNonNil :: renamedInitialPureFormula
                        else
                            renamedInitialPureFormula

                    let newState = partState.CreateExtension renamedInitialPredicates Seq.empty renamedInitialPureFormula !newExistentials
                    newRes <- newState :: newRes
        res <- newRes

    //We resolve the additional nilV == nil before returning:
    res
    |> List.map (fun s -> s.ResolveEqualities(); s.Simplify(); s)
    |> List.filter (fun s -> not s.IsContradictory)

let GuessInitialSymHeaps (varList: TypedVar list) nestLevel noNilInNested varCounter =
    ///Compute all possible nestings of type parameters up to a certain nestDepth
    let rec nestHigherOrderPred (symHeap : SymHeap) nestDepth =
        if nestDepth <= 0 then
            [symHeap]
        else

        let nestIntoPredicate (predicate : Predicate) =
            assert (predicate.TypeParameter.IsNone)

            //First, find out how many parameters the inner heap gets. This is in the expansion rule for the predicate:
            let expRule = expansionRules predicate.PredicateName
            let allParameters = ref []
            let nestableParameters = ref []
            for nestable in expRule.HigherOrderParameters do
                let newName = FreshRandomAddrVar varCounter "ini_v"
                allParameters := newName :: !allParameters
                if nestable then
                    nestableParameters := newName :: !nestableParameters
            let allParameters = List.rev !allParameters //Restore order!

            //now guess instantiations for the type parameter:
            let allVariables = (List.ofSeq (symHeap.AllVars)) @ allParameters
            let typeParInstantiations =
                [ for s in GuessFlatSymHeaps !nestableParameters allParameters allVariables false noNilInNested varCounter do
                    s.Simplify()
                    if not(s.Predicates.Count + s.PointsTos.Count + s.PureFormulas.Count = 0) then
                        yield s
                ]

            // Descend into the generated instantiations, and do some nesting there:
            typeParInstantiations
            |> List.collect (fun typeParInst -> nestHigherOrderPred typeParInst (nestDepth - 1))
            |> List.map (fun typeParInst -> Predicate(predicate.PredicateName, Some typeParInst, predicate.Arguments))
            |> (fun res -> predicate::res)

        //Expand all heaplets we have at the moment. Then, combine and create fresh results:
        Seq.map nestIntoPredicate symHeap.Predicates
        |> List.ofSeq
        |> Utils.cartesianProduct
        |> List.map (fun nestedPredicateCombination -> symHeap.ResetPredicates nestedPredicateCombination)

    // (2) construct set of "flat" sym heap, without type parameters describing the shape of values.
    let flatSymHeaps = GuessFlatSymHeaps varList varList varList true false varCounter

    // (3) take each symbolic heap and nest up to a certain level, then return:
    //     For all typed variables that have no defining heaplet, assume that they have to be Nil.
    let setUndefTypedVarsToNil (s : SymHeap) =
        let undefIsNilEqs = s.FreeVars |> Seq.filter (fun var -> s.IsUndefinedVariable var) |> Seq.map (fun v -> Relation(Eq, Var v, Nil))
        s.AddPure undefIsNilEqs

    let res = System.Collections.Generic.HashSet()
    for s in flatSymHeaps |> List.collect (fun symHeap -> nestHigherOrderPred symHeap nestLevel) do
        setUndefTypedVarsToNil s
        s.ResolveEqualities() |> ignore
        if not s.IsContradictory then
            res.Add (SymHeap.standardize s) |> ignore
    res

type SepLogicModelEnumerator  =
    (*
      We have two expansion steps:
       (1) resolving possible equalities
       (2) expanding predicates
      We alternate the two to finally obtain states without predicates, which we then concretise
      into a standard program heap.
    *)
    {
        InitialFormula : SymHeap
        FreeVariables : TypedVar seq
        ExistentialVariables : TypedVar seq
        ExpansionQueue : PriorityQueue<SymHeap * ListDictionary<TypedVar, TypedVar>>
        mutable CurPredLess : (SymHeap * ListDictionary<TypedVar, TypedVar>) list
        mutable CurFormula : (SymHeap * ListDictionary<TypedVar, TypedVar>) option
        mutable IsValid : bool 
        VarCounter : int ref
    }

    static member private symheapPriority ((state, _) : (SymHeap * ListDictionary<TypedVar, TypedVar>)) : int =
         - (state.Level + state.Predicates.Count)

    static member create formula freeVars exVars =
        let initialQueue = PriorityQueue SepLogicModelEnumerator.symheapPriority
        initialQueue.Push (formula, ListDictionary())
        { InitialFormula = formula
          FreeVariables = freeVars
          ExistentialVariables = exVars
          ExpansionQueue = initialQueue
          CurPredLess = []
          CurFormula = None
          IsValid = true
          VarCounter = ref 0
       }

    member self.MoveNext () =
        if not(self.IsValid) then
            raise (System.InvalidOperationException())

        //Loop and generate more states until we found one we can instantiate:
        let isDone = ref false
        while not(!isDone) do
            if List.isEmpty self.CurPredLess && PriorityQueue.isEmpty self.ExpansionQueue then
                isDone := true
                self.CurFormula <- None
                self.IsValid <- false
            else
                match self.CurPredLess with
                | (s, subheapStartToExVariables) :: restPredLess -> //we have a state: take that one
                    self.CurPredLess <- restPredLess
                    if not s.IsContradictory then
                        self.CurFormula <- Some (s, subheapStartToExVariables)
                        isDone := true
                | [] ->
                    let s = PriorityQueue.pop self.ExpansionQueue
                    let expanded = Expand self.VarCounter s
                    let (predLess, newSymStates) = List.partition (fun ((s, _) : (SymHeap * ListDictionary<TypedVar, TypedVar>)) -> s.IsPredless) expanded
                    //printfn "%i/%i new" (List.length predLess) (List.length newSymStates)
                    self.CurPredLess <- predLess
                    Seq.iter self.ExpansionQueue.Push newSymStates

        self.IsValid

    member self.CurrentFormula
        with get () =
            if self.CurFormula = None then
                if self.IsValid then
                    ignore <| self.MoveNext ()
                else
                    raise (System.InvalidOperationException())
            self.CurFormula.Value

    member self.Current
        with get () =
            let (formula, subheapStartToExVariables) = self.CurrentFormula
            Instantiate formula self.FreeVariables self.ExistentialVariables subheapStartToExVariables

    interface System.IDisposable with
        member __.Dispose () = ()
    interface System.Collections.IEnumerator with
        member self.Reset () =
            self.ExpansionQueue.Clear()
            self.ExpansionQueue.Push (self.InitialFormula, ListDictionary())
            self.CurPredLess <- []
            self.CurFormula <- None
            self.VarCounter := 0
        member self.MoveNext () =
            self.MoveNext ()
        member self.Current with get () = box self.Current
    interface System.Collections.Generic.IEnumerator<State * (Map<TypedVar, Addr> * ListDictionary<Addr, Addr>)> with
        member self.Current with get () = self.Current
    interface System.Collections.IEnumerable with
        member self.GetEnumerator () = self :> System.Collections.IEnumerator
    interface System.Collections.Generic.IEnumerable<State * (Map<TypedVar, Addr> * ListDictionary<Addr, Addr>)> with
        member self.GetEnumerator () = self :> _