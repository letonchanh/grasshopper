module SyntaxTree

open Utils
open SepLogic

type NodeType =
    | Symheap
    | ExistentialBinding
    | Heaplets
    | Heaplet
    | EmptyHeaplet
    | TypedHeaplet of SepLogic.PredicateName
    | LambdaBinding
    | EmptyLambdaBinding
    | TypedLambdaBinding of SepLogic.PredicateName
    | Expression
    | Variable
    | Comma
    | Pipe
    | Period
    | SepStar
    | PointsToSymbol
    | LParen
    | RParen
    | LBrace
    | RBrace
    | Lambda
    | Exists
    | NULL //Technical reasons...
    | PredicateId of SepLogic.PredicateName
    | ExpressionId of string
    | PureFormula
    | PureRelation
    | Colon
    | Conjunction
    | Eq
    | Ne
    | True
    | FieldId of string
    | FieldDeref
    | BtwnPred
    | Btwn
    | StringLiteral of string
    | AccPred
    | Acc

    override self.ToString() =
        match self with
        | Symheap -> "symheap"
        | ExistentialBinding -> "ex-binding"
        | Heaplets -> "heaplets"
        | Heaplet -> "heaplet"
        | EmptyHeaplet -> "emp"
        | TypedHeaplet s -> sprintf "%s-heaplet" (s.ToString())
        | LambdaBinding -> "lambda-binding"
        | EmptyLambdaBinding -> "_"
        | TypedLambdaBinding s -> sprintf "%s-lambda" (s.ToString())
        | Variable -> "var"
        | Expression -> "expr"
        | Comma -> ","
        | Period -> "."
        | Pipe -> "|"
        | SepStar -> "*"
        | PointsToSymbol -> "->"
        | LParen -> "("
        | RParen -> ")"
        | LBrace -> "{"
        | RBrace -> "}"
        | Lambda -> "\\"
        | Exists -> "Ex."
        | NULL -> "NULL"
        | PredicateId s -> s.ToString()
        | ExpressionId s -> s
        | PureFormula -> "pure-formula"
        | PureRelation -> "relation"
        | Colon -> ":"
        | Conjunction -> "&&"
        | Eq -> "=="
        | Ne -> "<>"
        | True -> "true"
        | FieldId f -> f
        | FieldDeref -> "."
        | BtwnPred -> "btwn-pred"
        | Btwn-> "Btwn"
        | AccPred -> "acc-pred"
        | Acc -> "acc"
        | StringLiteral s -> "\"" + s + "\""

    member self.IsTypedHeapl =
        match self with
        | TypedHeaplet _ -> true
        | _ -> false

    member self.IsTypedLambda =
        match self with
        | TypedLambdaBinding _ -> true
        | _ -> false

    member self.IsExpr =
        match self with | Expression -> true | _ -> false
    member self.IsVar =
        match self with | Variable -> true | _ -> false
    member self.IsPred =
        match self with | PredicateId _ -> true | _ -> false

    member self.IsTerminal =
        match self with
        | EmptyLambdaBinding
        | EmptyHeaplet
        | Comma
        | Pipe
        | Period
        | SepStar
        | PointsToSymbol
        | LParen
        | RParen
        | LBrace
        | RBrace
        | Lambda
        | Exists
        | ExpressionId _
        | PredicateId _
        | Colon
        | Conjunction
        | Eq
        | Ne
        | True
        | FieldDeref
        | FieldId _
        | Btwn
        | Acc
        | StringLiteral _
            -> true
        | _ -> false

let private NodeCounter = ref 0
type Node(nodeType : NodeType) =
    let id : int =
        lock
            NodeCounter
            (fun _  ->
                incr NodeCounter
                !NodeCounter)

    member __.Id = id
    member __.NodeType = nodeType
    member __.IsTerminal = nodeType.IsTerminal

    static member GetId (n : Node) = n.Id
    static member GetNodeType (n : Node) = n.NodeType

    override self.Equals other = equalsOn Node.GetId self other
    override self.GetHashCode () = hash self.Id
    member self.IdIndepEquals other = equalsOn Node.GetNodeType self other
    member self.GetIdIndepHashCode () = hash self.NodeType
    interface System.IComparable with
        member self.CompareTo other = compareOn Node.GetId self other

    override self.ToString () =
        sprintf "%i:%s " self.Id (self.NodeType.ToString())

    member self.GetNameFromExpressionId =
        match self.NodeType with
        | ExpressionId s -> s
        | _ -> invalidArg "node" "Is not an expression node."

/// ~ Syntax Tree Production
type STProduction (nodeList : System.Collections.Generic.List<NodeType>) =
    member private __.NodeList
        with get () = nodeList

    override __.Equals otherObject =
        match otherObject with
        | :? STProduction as prod ->
            System.Linq.Enumerable.SequenceEqual (nodeList, prod.NodeList)
        | :? System.Collections.Generic.List<NodeType> as prodList ->
            System.Linq.Enumerable.SequenceEqual (nodeList, prodList)
        | _ -> false

    override __.GetHashCode () =
        nodeList |> Seq.fold (fun hash item -> hash * 31 + item.GetHashCode()) 23

    interface System.Collections.Generic.IEnumerable<NodeType> with
        member __.GetEnumerator () = nodeList.GetEnumerator () :> _
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = nodeList.GetEnumerator () :> _

    override __.ToString () =
        nodeList |> Seq.map (fun n -> n.ToString()) |> String.concat " "

// syntax tree corresponding to a separation logic formula
[<CustomEquality;CustomComparison>]
type SyntaxTree =
    {
        root : Node
        nodes : System.Collections.Generic.HashSet<Node>
        childToParentMap : System.Collections.Generic.Dictionary<Node, Node>
        parentToChildrenMap : System.Collections.Generic.Dictionary<Node, System.Collections.Generic.List<Node>>
    }
    with

    member self.GetChildren v =
        self.parentToChildrenMap.GetWithDefault v (System.Collections.Generic.List<Node>())
    member self.GetChildrenTuple v = self.GetChildren v |> Seq.toArray
    member self.GetParent v = self.childToParentMap.TryFind v
    member self.GetDepth v =
        let mutable curNode = v
        let mutable depth = 0
        while self.childToParentMap.ContainsKey curNode do
            curNode <- self.childToParentMap.[curNode]
            depth <- depth + 1
        depth

    member self.GetOrderList () = self.nodes |> List.ofSeq |> List.sortBy Node.GetId

    member self.IsLeafNode n = not(self.parentToChildrenMap.ContainsKey n) || self.parentToChildrenMap.[n].Count = 0
    member self.GetLeafNodes () = self.nodes |> Seq.filter self.IsLeafNode
    member self.IsExpandable () = not(self.GetLeafNodes () |> Seq.forall (function e -> e.IsTerminal))

    override self.GetHashCode () =
        self.childToParentMap |> Seq.fold (fun hash kv -> hash ^^^ (kv.Key.GetIdIndepHashCode() + 31 * kv.Value.GetIdIndepHashCode())) 23
    override self.Equals other =
        match other with
        | :? SyntaxTree as otherTree ->
            Seq.zip self.childToParentMap otherTree.childToParentMap
            |> Seq.forall (fun (kv1, kv2) -> kv1.Key.IdIndepEquals kv2.Key && kv1.Value.IdIndepEquals kv2.Value)
        | _ -> false
    interface System.IComparable with
        member self.CompareTo obj =
            match obj with
            | :? SyntaxTree as otherTree ->
                compare (self.GetHashCode()) (otherTree.GetHashCode())
            | _ -> invalidArg "obj" "Comparing with an object of different type"

    static member Empty : SyntaxTree =
        let rootNode = Node Symheap
        {
            root = rootNode ;
            nodes = System.Collections.Generic.HashSet([rootNode])
            childToParentMap = System.Collections.Generic.Dictionary()
            parentToChildrenMap = System.Collections.Generic.Dictionary()
        }

    member self.AddEdge v1 v2 =
        self.nodes.Add v1 |> ignore
        self.nodes.Add v2 |> ignore
        self.childToParentMap.[v2] <- v1
        let mutable existingChildren = null
        if self.parentToChildrenMap.TryGetValue (v1, &existingChildren) then
            existingChildren.Add v2
        else
            self.parentToChildrenMap.[v1] <- System.Collections.Generic.List([v2])

    member self.ReplaceSubtree v1 v2 =
        //Delete all nodes below v1:
        let v1Parent = (self.GetParent v1).Value
        let mutable stack = [v1]
        while not (List.isEmpty stack) do
            let curNode = List.head stack
            stack <- List.tail stack
            self.childToParentMap.Remove curNode |> ignore
            if self.parentToChildrenMap.ContainsKey curNode then
                stack <- (self.GetChildren curNode |> List.ofSeq) @ stack
                self.parentToChildrenMap.Remove curNode |> ignore

        //Do the actual replacement:
        let v1ParentChildren = self.parentToChildrenMap.[v1Parent]
        let v1Index = v1ParentChildren.FindIndex(System.Predicate((=) v1))
        v1ParentChildren.[v1Index] <- v2
        self.childToParentMap.[v2] <- v1Parent

    override self.ToString () = self.ToString false
    member self.ToCanonicalString () = self.ToString true

    member private self.ToString (canonicalize : bool) =
        let res = System.Text.StringBuilder()
        let mutable varCounter = 0
        let varNormalizer = System.Collections.Generic.Dictionary()
        let getNormalizedVarName var =
            if "nil" = var then
                "nil"
            else
                match varNormalizer.TryGetValue var with
                | (true, newName) -> newName
                | (false, _) -> var

        let mutable stack = [self.root]
        while not(List.isEmpty stack) do
            let curNode = List.head stack
            stack <- List.tail stack

            if curNode.IsTerminal then
                //Prefix
                match curNode.NodeType with
                | Colon
                | PointsToSymbol
                | Pipe
                | SepStar
                | Eq
                | Ne
                | Conjunction
                    -> res.Append " " |> ignore
                | _ -> ()
                //Actual value
                match curNode.NodeType with
                | ExpressionId i -> res.Append (getNormalizedVarName i) |> ignore
                | _ -> res.Append (curNode.NodeType.ToString()) |> ignore
                //Postfix
                match curNode.NodeType with
                | Colon
                | Comma
                | Pipe
                | Exists
                | Period
                | PointsToSymbol
                | SepStar
                | Eq
                | Ne
                | Conjunction
                    -> res.Append " " |> ignore
                | _ -> ()
            else
                let children =
                    match self.parentToChildrenMap.TryGetValue curNode with
                    | (true, children) ->
                        try
                            match curNode.NodeType with
                            | ExistentialBinding ->
                                if canonicalize then
                                    //Get variable children, rename:
                                    for varChild in children |> Seq.filter (fun n -> n.NodeType = Variable) do
                                        let name = self.GetNameFromExpressionNode varChild
                                        varNormalizer.[name] <- "v" + string varCounter
                                        varCounter <- varCounter + 1
                                    children
                                else children
                            | TypedLambdaBinding typ ->
                                let varChildren = children |> Seq.filter (fun n -> n.NodeType = Variable)
                                if canonicalize then
                                    //Get variable children, rename. One horrible deviation: in ls(x, y, \ v1 v2 v3 v4), v2 is always y. Hence, we do that in the var renaming...
                                    for varChild in varChildren do
                                        let name = self.GetNameFromExpressionNode varChild
                                        varNormalizer.[name] <- "v" + string varCounter
                                        varCounter <- varCounter + 1
                                match typ with
                                | List ->
                                    let secondLambdaVar = Seq.head (Seq.skip 1 varChildren) |> self.GetNameFromExpressionNode
                                    let parentParentNode = (self.GetParent (self.GetParent curNode).Value).Value //This is the enclosing TypedHeaplet of type list
                                    let secondArgumentName = self.GetChildren parentParentNode |> Seq.filter (fun n -> n.NodeType = Expression) |> Seq.skip 1 |> Seq.head |> self.GetNameFromExpressionNode
                                    varNormalizer.[secondLambdaVar] <- getNormalizedVarName secondArgumentName
                                | _ -> ()
                                children
                            | Heaplets ->
                                if canonicalize then
                                    //Reorder by name of defined variable
                                    let getDefinedVariable node =
                                        let spatialAtomNode = (self.GetChildren node |> Seq.head)
                                        let definedVarNode = (self.GetChildren spatialAtomNode |> Seq.filter (fun n -> n.NodeType = Expression) |> Seq.head)
                                        let definedVar = self.GetNameFromExpressionNode definedVarNode
                                        getNormalizedVarName definedVar
                                    let allHeapletChildren = System.Collections.Generic.List()
                                    let mutable curChildren = children
                                    while curChildren.Count >= 3 && curChildren.[2].NodeType = Heaplets do
                                        allHeapletChildren.Add curChildren.[0]
                                        curChildren <- self.parentToChildrenMap.GetWithDefault curChildren.[2] (new System.Collections.Generic.List<Node>())
                                    let reorderedChildren = System.Collections.Generic.List()
                                    let mutable isFirst = true
                                    for heaplet in allHeapletChildren |> Seq.sortBy getDefinedVariable do
                                        if isFirst then
                                            isFirst <- false
                                        else
                                            reorderedChildren.Add (Node SepStar)
                                        reorderedChildren.Add heaplet
                                    reorderedChildren
                                else children
                            | PureFormula ->
                                if canonicalize then
                                    let reorderedChildren = System.Collections.Generic.List()
                                    reorderedChildren.Add (Node True) //Ignore pure part in canonical representation
                                    reorderedChildren
                                else children
                            | _ -> children
                        with
                        | :? System.ArgumentException -> children
                        | :? System.Collections.Generic.KeyNotFoundException -> children
                    | (false, _) -> System.Collections.Generic.List()
                for i in children.Count - 1 .. -1 .. 0 do
                    let child = children.[i]
                    stack <- child :: stack

        res.ToString()

    member self.ToStringDetailed () =
        let res = System.Text.StringBuilder()
        res.AppendLine(self.ToString()) |> ignore
        let rec dfs (node: Node) indent =
            let prefix = String.replicate indent "|   "
            res.AppendFormat("{0}{1}\n", prefix, node.ToString()) |> ignore
            for child in self.GetChildren node do
                dfs child (indent + 1)
        dfs self.root 0
        res.ToString()

    member self.TryGetNameFromExpressionNode (exprNode : Node) =
        let children = self.GetChildren exprNode
        if children.Count > 0 then
            Some children.[0].GetNameFromExpressionId
        else
            None

    member self.GetNameFromExpressionNode (exprNode : Node) =
        (self.TryGetNameFromExpressionNode exprNode).Value

    member self.GetTypedHeapletArguments (typedHeapletNode : Node) =
        self.GetChildren typedHeapletNode
        |> Seq.filter (fun (n : Node) -> n.NodeType.IsExpr)

    member self.ToDot outStream =
        fprintfn outStream "digraph syntaxtree {"

        let mutable potentialEdges = []
        for node in self.nodes do
            let varID = node.Id
            let varName = node.NodeType.ToString()
            if node.IsTerminal then
                fprintfn outStream " var%i [shape=record, style=\"filled, round\", fillcolor=yellow, label=\"[%i] %s\"];" varID varID varName
            else
                fprintfn outStream " var%i [shape=ellipse, color=black, label=\"[%i] %s\"];" varID varID varName
            if self.childToParentMap.ContainsKey node then
                let parent = self.childToParentMap.[node]
                potentialEdges <- (sprintf "var%i" parent.Id, sprintf "var%i" node.Id) :: potentialEdges

        for (src, dst) in potentialEdges do
            fprintfn outStream " %s -> %s [label=\"\"];" src dst

        fprintfn outStream "};"

    ///Identify all variables in scope at this node, i.e. variables bound in lambdas / existentials.
    member self.GetDefinableVariablesInScope (node : Node) : (bool * SepLogic.VarName list) =
        let mutable res = []
        let mutable curNode = Some node
        let mutable isInInner = false
        while curNode.IsSome do
            match curNode.Value.NodeType with
            | TypedLambdaBinding predType ->
                let variablesDefinable = (SepLogic.expansionRules predType).HigherOrderParameters
                for (definable, varNode) in self.GetChildren curNode.Value |> Seq.filter (fun n -> n.NodeType.IsVar) |> Seq.zip variablesDefinable do
                    if definable then
                        res <- (self.GetNameFromExpressionNode varNode) :: res
                //Don't go up in the tree. While in principle something from the outside may be definable here, it wouldn't make any sense.
                isInInner <- true
                curNode <- None
            | ExistentialBinding ->
                for varNode in self.GetChildren curNode.Value do
                    if varNode.NodeType.IsVar then
                        res <- (self.GetNameFromExpressionNode varNode) :: res
                curNode <- self.GetParent curNode.Value //Continue walking upwards
            | _ ->
                curNode <- self.GetParent curNode.Value //Continue walking upwards
        (isInInner, res)

    ///Get nodes of "defined" variables (i.e., those that are in the first position of a predicate), outermost comes last in result
    member self.GetEnclosingDefinedVariableNodes (node : Node) =
        let mutable res = []
        let mutable curNode = Some node
        //Walk up the syntax tree, looking for predicate-containing *-heaplet nodes. The first "expr" child of those is the defined variable
        while curNode.IsSome do
            if curNode.Value.NodeType.IsTypedHeapl then
                let definedVarNode =
                    self.GetChildren curNode.Value
                    |> Seq.filter (fun (childNode : Node) -> childNode.NodeType.IsExpr)
                    |> Seq.minBy (fun (node : Node) -> node.Id)
                if definedVarNode <> node then
                    res <- (self.GetChildren definedVarNode |> Seq.head) :: res
            curNode <- self.GetParent curNode.Value
        List.rev res

    ///Return the list of variables that are defined above / to the left of this node
    member self.GetAlreadyDefinedVariables node =
        let mutable res = []

        //Traverse the tree upward. Whenever we hit a heaplet node, we look to the left to check out our older siblings
        let mutable prevNode = node
        let mutable curNode = self.GetParent node
        while curNode.IsSome do
            match curNode with
            | Some curNode ->
                match curNode.NodeType with
                | Heaplets -> //Case: We are inside some heaplets, but there are heaplets to the left of us
                    for otherChild in self.GetChildren curNode do
                        if otherChild.Id < prevNode.Id && otherChild.NodeType = Heaplet then //it's to the left!
                            let otherChildChild = self.GetChildren otherChild |> Seq.head
                            match otherChildChild.NodeType with //Get at the typled heaplet node...
                            | TypedHeaplet _ ->
                                let definedExpressionNode = self.GetChildren otherChildChild |> Seq.find (fun n -> n.NodeType.IsExpr)
                                if definedExpressionNode <> node then
                                    res <- self.GetNameFromExpressionNode definedExpressionNode :: res
                            | _ -> ()
                | TypedHeaplet _ -> //Case: We are inside a typed heaplet, which maybe already has a defined variable
                    let definedExpressionNode = self.GetChildren curNode |> Seq.tryFind (fun n -> n.NodeType.IsExpr)
                    match definedExpressionNode with
                    | Some definedExpressionNode when definedExpressionNode <> node ->
                        res <- self.GetNameFromExpressionNode definedExpressionNode :: res
                    | _ -> ()
                | _ -> ()
            | _ -> ()
            prevNode <- curNode.Value
            curNode <- self.GetParent curNode.Value

        res

    member self.GetDefinedToReachableVariables (node : Node) =
        let res = SetDictionary()

        let extractDefinedAndReachables typedHeapletNode =
            let childExpressions = self.GetChildren typedHeapletNode |> Seq.filter (fun n -> n.NodeType.IsExpr) |> List.ofSeq
            if childExpressions.Length > 0 then
                let definedExpressionNode = childExpressions.[0]
                match self.TryGetNameFromExpressionNode definedExpressionNode with
                | None -> ()
                | Some definedVariable ->
                    childExpressions
                    |> Seq.skip 1
                    |> Seq.filter (fun childNode -> childNode.Id < node.Id)
                    |> Seq.map self.TryGetNameFromExpressionNode
                    |> Seq.iter (function | None -> () | Some childVariable -> res.Add (definedVariable, childVariable) |> ignore)

        //Traverse the tree upward. Whenever we hit a heaplet node, we look to the left to check out our older siblings
        let mutable prevNode = node
        let mutable curNode = self.GetParent node
        while curNode.IsSome do
            match curNode with
            | Some curNode ->
                match curNode.NodeType with
                | Heaplets -> //Case: We are inside some heaplets, but there are heaplets to the left of us
                    for otherChild in self.GetChildren curNode do
                        if otherChild.Id < prevNode.Id && otherChild.NodeType = Heaplet then //it's to the left!
                            let otherChildChild = self.GetChildren otherChild |> Seq.head
                            match otherChildChild.NodeType with //Get at the typled heaplet node...
                            | TypedHeaplet _ ->
                                extractDefinedAndReachables otherChildChild
                            | _ -> ()
                | TypedHeaplet _ -> //Case: We are inside a typed heaplet, which maybe already has a defined variable
                    extractDefinedAndReachables curNode
                | _ -> ()
            | _ -> ()
            prevNode <- curNode.Value
            curNode <- self.GetParent curNode.Value

        res

    member self.GetExprNodePosDescriptor (node : Node) =
        assert (node.NodeType = Expression)
        let parentNode = (self.GetParent node).Value
        let enclosingPredicate =
            match parentNode.NodeType with
            | TypedHeaplet name -> name.ToString()
            | _                 -> failwith "Unexpected syntax tree structure"
        let argPosition =
            self.GetChildren parentNode
            |> Seq.filter (fun (n : Node) -> n.NodeType = Expression)
            |> Seq.findIndex (fun (n : Node) -> n.Id = node.Id)
        sprintf "expr_%s_%i" enclosingPredicate argPosition

    /// Construct a SyntaxTree from a separation logic formula.
    static member fromSepLogicFormula (fml : SepLogic.SymHeap) =

        let variableNameNormaliser = System.Collections.Generic.Dictionary()
        fml.FreeVars |> Seq.iter (fun v -> variableNameNormaliser.[v.Name] <- v.Name)
        let varIdx = ref 1
        let normaliseVarName n =
            match variableNameNormaliser.TryGetValue n with
            | (true, n') -> n'
            | (false, _) ->
                let newName = "v" + string !varIdx
                varIdx := !varIdx + 1
                variableNameNormaliser.Add (n, newName)
                newName

        //Recursive transformation into a Syntax tree.
        //We want to mirror the production process in the order of things.
        //To this, every (non-terminal) node is first connected to its parent, then its children are generated from left to right,
        //and then recursively processed in that order.
        let rec addSymHeap (heap : SepLogic.SymHeap) (syntaxTree : SyntaxTree) (parentNode : Node) =
            let mutable lastParentNode = parentNode

            //First, insert a chain of nodes for the existential bindings:
            for quantifiedVar in heap.ExVars do
                let quantifierNode = Node ExistentialBinding
                syntaxTree.AddEdge lastParentNode quantifierNode

                syntaxTree.AddEdge quantifierNode (Node Exists)
                let varNode = Node Variable
                syntaxTree.AddEdge quantifierNode varNode
                syntaxTree.AddEdge varNode (Node (ExpressionId (normaliseVarName quantifiedVar.Name)))
                syntaxTree.AddEdge quantifierNode (Node Period)
                lastParentNode <- quantifierNode

            //Insert the pure formula as first child, then the separating colon, then the spatial formula:
            let pureFormulaNode = Node PureFormula
            syntaxTree.AddEdge lastParentNode pureFormulaNode
            addPureFormula heap.PureFormulas syntaxTree pureFormulaNode
            syntaxTree.AddEdge lastParentNode (Node Colon)
            addHeaplets heap syntaxTree lastParentNode

        and addHeaplets heap syntaxTree parentNode =
            //Insert the heaplets, bit by bit:
            let mutable heapletsNode = Node Heaplets
            syntaxTree.AddEdge parentNode heapletsNode

            let upcastToSpatialFormula = fun s -> s :> SpatialFormula
            let predicates = heap.Predicates |> Seq.sortBy (fun (pred : Predicate) -> pred.PredicateName.ToString() + pred.Arguments.Head.ToString()) |> Seq.map upcastToSpatialFormula
            let pointsTos = heap.PointsTos |> Seq.sortBy (fun (pTo : PointsTo) -> pTo.DefinedVariable.ToString()) |> Seq.map upcastToSpatialFormula
            for (heapletInfo : SpatialFormula) in Seq.append predicates pointsTos do
                let heapletNode = Node Heaplet
                syntaxTree.AddEdge heapletsNode heapletNode
                match heapletInfo with
                | :? Predicate as predicate -> addPredicate predicate syntaxTree heapletNode
                | :? PointsTo as pointsTo -> addPointsTo pointsTo syntaxTree heapletNode
                | _ -> failwith "unknown spatial formula encountered"
                syntaxTree.AddEdge heapletsNode (Node SepStar)
                let newHeapletsNode = Node Heaplets
                syntaxTree.AddEdge heapletsNode newHeapletsNode
                heapletsNode <- newHeapletsNode
            syntaxTree.AddEdge heapletsNode (Node EmptyHeaplet)

        and addPureFormula (pureFormulas : PureFormula seq) (syntaxTree : SyntaxTree) (parentNode : Node) =
            if Seq.isEmpty pureFormulas then
                syntaxTree.AddEdge parentNode (Node True)
            else
                let mutable isFirst = true
                for pureFormula in pureFormulas do
                    if isFirst then
                        isFirst <- false
                    else
                        syntaxTree.AddEdge parentNode (Node Conjunction)

                    match pureFormula with
                    | Relation (relType, e1, e2) ->
                        let relationNode = Node PureRelation
                        syntaxTree.AddEdge parentNode relationNode

                        let leftExprNode = Node Expression
                        syntaxTree.AddEdge relationNode leftExprNode
                        addExpr e1 syntaxTree leftExprNode

                        match relType with
                        | SepLogic.Eq -> syntaxTree.AddEdge relationNode (Node Eq)
                        | SepLogic.Ne -> syntaxTree.AddEdge relationNode (Node Ne)

                        let rightExprNode = Node Expression
                        syntaxTree.AddEdge relationNode rightExprNode
                        addExpr e2 syntaxTree rightExprNode

        and addPointsTo (pointsTo : SepLogic.PointsTo) (syntaxTree : SyntaxTree) (parentNode : Node) =
            let pointsToNode = Node PointsToSymbol
            syntaxTree.AddEdge parentNode pointsToNode

            syntaxTree.AddEdge pointsToNode (Node LParen)
            let exprNode = Node Expression
            syntaxTree.AddEdge pointsToNode exprNode
            addExpr pointsTo.DefinedVariable syntaxTree exprNode
            for valueElement in pointsTo.Arguments do
                syntaxTree.AddEdge pointsToNode (Node Comma)
                let exprNode = Node Expression
                syntaxTree.AddEdge pointsToNode exprNode
                addExpr valueElement syntaxTree exprNode
            syntaxTree.AddEdge pointsToNode (Node RParen)

        and addPredicate (predicate : SepLogic.Predicate) (syntaxTree : SyntaxTree) (parentNode : Node) =
            let predicateHeapletNode = Node (TypedHeaplet predicate.PredicateName)
            syntaxTree.AddEdge parentNode predicateHeapletNode

            syntaxTree.AddEdge predicateHeapletNode (Node (PredicateId (predicate.PredicateName)))
            syntaxTree.AddEdge predicateHeapletNode (Node LParen)
            let mutable isFirst = true
            for valueElement in predicate.Arguments do
                if not isFirst then
                    syntaxTree.AddEdge predicateHeapletNode (Node Comma)
                isFirst <- false
                let exprNode = Node Expression
                syntaxTree.AddEdge predicateHeapletNode exprNode
                addExpr valueElement syntaxTree exprNode

            syntaxTree.AddEdge predicateHeapletNode (Node Pipe)
            let lambdaNode = Node LambdaBinding
            syntaxTree.AddEdge predicateHeapletNode lambdaNode
            ///// Now finally go on to the subheap:
            match predicate.TypeParameter with
            | None ->
                syntaxTree.AddEdge lambdaNode (Node EmptyLambdaBinding)
            | Some subFormula ->
                let typedLambdaNode = Node (TypedLambdaBinding predicate.PredicateName)
                syntaxTree.AddEdge lambdaNode typedLambdaNode
                syntaxTree.AddEdge typedLambdaNode (Node Lambda)
                let mutable isFirst = true
                for varArgument in subFormula.FreeVars do
                    if not isFirst then
                        syntaxTree.AddEdge typedLambdaNode (Node Comma)
                    isFirst <- false
                    let varNode = Node Variable
                    syntaxTree.AddEdge typedLambdaNode varNode
                    syntaxTree.AddEdge varNode (Node (ExpressionId (normaliseVarName varArgument.Name)))
                syntaxTree.AddEdge typedLambdaNode (Node PointsToSymbol)
                let subSymHeapNode = Node Symheap
                syntaxTree.AddEdge typedLambdaNode subSymHeapNode
                addSymHeap subFormula syntaxTree subSymHeapNode
            syntaxTree.AddEdge predicateHeapletNode (Node RParen)
        and addExpr (expr : SepLogic.Expr) (syntaxTree : SyntaxTree) (parentNode : Node) =
            match expr with
            | Nil            -> syntaxTree.AddEdge parentNode (Node (ExpressionId "nil"))
            | SepLogic.Var v -> syntaxTree.AddEdge parentNode (Node (ExpressionId (normaliseVarName v.Name)))

        let syntaxTree = SyntaxTree.Empty
        addSymHeap fml syntaxTree syntaxTree.root
        (syntaxTree, variableNameNormaliser)

type ProductionStore () =
    let nodeTypeToIdToProduction : (System.Collections.Concurrent.ConcurrentDictionary<NodeType, System.Collections.Concurrent.ConcurrentDictionary<int, STProduction>>) =
        System.Collections.Concurrent.ConcurrentDictionary()

    member __.GetIdToProduction nodeType =
        match nodeTypeToIdToProduction.TryGetValue nodeType with
        | (true, res) -> res
        | (false, _) ->
            let newRes = System.Collections.Concurrent.ConcurrentDictionary()
            nodeTypeToIdToProduction.[nodeType] <- newRes
            newRes

    member self.NoteProduction nodeType production =
        let idToProduction = self.GetIdToProduction nodeType
        match idToProduction |> Seq.tryFind (fun kv -> production.Equals kv.Value) with
        | Some (KeyValue (id, _)) ->
            id
        | None ->
            lock idToProduction
                (fun _ ->
                    //Now get next free ID, and on the way, recheck that a racing thread
                    //hasn't solved the problem for us:
                    let mutable maxId = -1
                    let mutable foundId = None
                    for KeyValue(id, storedProd) in idToProduction do
                        maxId <- max id maxId
                        if production.Equals storedProd then
                            foundId <- Some id
                    let newId =
                        match foundId with
                        | None -> maxId + 1
                        | Some id -> id
                    idToProduction.[newId] <- production
                    newId)

    member self.GetProduction nodeType id =
        let idToProduction = self.GetIdToProduction nodeType
        match idToProduction.TryGetValue id with
        | (true, production) -> production
        | (false, _) -> invalidArg "nodeType / id" (sprintf "No production with id %i known for node type %A" id nodeType)

    member __.GetNodeTypes () =
        nodeTypeToIdToProduction
        |> Seq.map (fun kv -> kv.Key)

    member __.GetNonTrivialNodeTypes () =
        nodeTypeToIdToProduction
        |> Seq.filter (fun kv -> kv.Value.Count > 1)
        |> Seq.map (fun kv -> kv.Key)