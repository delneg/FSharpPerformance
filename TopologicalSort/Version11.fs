module TopologicalSort.Version11
#nowarn "9"

(*
Version 9:

*)

open System
open System.Collections.Generic
open System.Numerics
open System.Runtime.CompilerServices
open System.Threading.Tasks
open FSharp.NativeInterop
open Row

     
let inline stackalloc<'a when 'a: unmanaged> (length: int): Span<'a> =
  let p = NativePtr.stackalloc<'a> length |> NativePtr.toVoidPtr
  Span<'a>(p, length)

let inline retype (x: 'T) : 'U = (# "" x: 'U #)

module Array =
    let inline stripUoM (x: '``Num<'M>`` []) =
        let _ = Unchecked.defaultof<'``Num<'M>``> * (LanguagePrimitives.GenericOne : 'Num)
        retype x :'Num []
        

[<RequireQualifiedAccess>]
module private Units =

    [<Measure>] type Node
    [<Measure>] type Edge
    [<Measure>] type Index


type Index = int<Units.Index>

module Index =
        
    let inline create (i: int) =
        if i < 0 then
            invalidArg (nameof i) "Cannot have an Index less than 0"
            
        LanguagePrimitives.Int32WithMeasure<Units.Index> i


type Node = int<Units.Node>

module Node =
    
    let inline create (i: int) =
        if i < 0 then
            invalidArg (nameof i) "Cannot have a Node less than 0"
            
        LanguagePrimitives.Int32WithMeasure<Units.Node> i


type Edge = int64<Units.Edge>

module Edge =

    let inline create (source: Node) (target: Node) =
        (((int64 source) <<< 32) ||| (int64 target))
        |> LanguagePrimitives.Int64WithMeasure<Units.Edge>
        
    let inline getSource (edge: Edge) =
        ((int64 edge) >>> 32)
        |> int
        |> LanguagePrimitives.Int32WithMeasure<Units.Node>

    let inline getTarget (edge: Edge) =
        int edge
        |> LanguagePrimitives.Int32WithMeasure<Units.Node>
    
    let inline getSourceBatch (vedge: Vector<int64>) =
        Vector.ShiftRightArithmetic(vedge, 32) |> Vector.AsVectorInt32

    let inline getTargetBatch (vedge: Vector<int64>) =
        vedge |> Vector.AsVectorInt32
    
[<IsByRefLike; Struct>]
type EdgeTracker (nodeCount: int, values: Span<uint64>) =
    
//    [<DefaultValue>] val mutable ValuesCount: int voption
    // Public for the purposes of inlining
    //bucket * offset * mask 
    member b.SourceTargetCache = Dictionary<int64, struct (int*int*uint64)>()
    member b.NodeCount = nodeCount
    member b.Values = values
//    member b.Filter = FilterBuilder.Build(b.NodeCount, 0.01, EdgeTracker.algo) 
    
    member inline b.GetSourceAndTargetData(edge: Edge) =
        if b.SourceTargetCache.ContainsKey(int64 edge) then
            b.SourceTargetCache[int64 edge]
        else
            let source = Edge.getSource edge
            let target = Edge.getTarget edge
            let location = (int source) * b.NodeCount + (int target)
            let bucket = location >>> 6
            let offset = location &&& 0x3F
            let mask = 1UL <<< offset
            let s = struct (bucket,offset,mask)
            b.SourceTargetCache.Add(int64 edge, s)
            s
    
    member inline b.Add (edge: Edge) =
        let source = Edge.getSource edge
        let target = Edge.getTarget edge
        let location = (int source) * b.NodeCount + (int target)
        
        let bucket = location >>> 6
        let offset = location &&& 0x3F
        let mask = 1UL <<< offset
//        b.Filter.Add(int64 edge) |> ignore
//        let struct (bucket, _,mask) = b.GetSourceAndTargetData(edge)
        b.Values[bucket] <- b.Values[bucket] ||| mask
    
    member inline b.BatchAdd(edge: Vector<int64>) =
        let sources = Edge.getSourceBatch edge
        let targets = Edge.getTargetBatch edge
        let locations = sources * b.NodeCount + targets
        let locationsArr: Span<int> = GC.AllocateUninitializedArray(64).AsSpan()
        locations.CopyTo(locationsArr)
        for location in locationsArr do
            let bucket = location >>> 6
            let offset = location &&& 0x3F
            let mask = 1UL <<< offset
            b.Values[bucket] <- b.Values[bucket] ||| mask
        
    member inline b.Remove (edge: Edge) =
        let source = Edge.getSource edge
        let target = Edge.getTarget edge
        let location = (int source) * b.NodeCount + (int target)
        let bucket = location >>> 6
        let offset = location &&& 0x3F
        let mask = 1UL <<< offset
//        let struct (bucket, _,mask) = b.GetSourceAndTargetData(edge)
        b.Values[bucket] <- b.Values[bucket] &&& ~~~mask

    member inline b.NotContains (edge: Edge) =
//        let struct (bucket, offset,_) = b.GetSourceAndTargetData(edge)
        let source = Edge.getSource edge
        let target = Edge.getTarget edge
        let location = (int source) * b.NodeCount + (int target)
        let bucket = location >>> 6
        let offset = location &&& 0x3F
        ((b.Values[bucket] >>> offset) &&& 1UL) <> 1UL
        
    member inline b.Contains (edge: Edge) =
//        let struct (bucket, offset,_) = b.GetSourceAndTargetData(edge)
        let source = Edge.getSource edge
        let target = Edge.getTarget edge
        let location = (int source) * b.NodeCount + (int target)
        let bucket = location >>> 6
        let offset = location &&& 0x3F
        ((b.Values[bucket] >>> offset) &&& 1UL) = 1UL
        
    member b.Clear () =
        for i = 0 to b.Values.Length - 1 do
            b.Values[i] <- 0UL

    member inline b.Count =
//        match b.ValuesCount with
//        | ValueSome x -> x
//        | ValueNone ->
            let mutable count = 0
            for i = 0 to b.Values.Length - 1 do            
                count <- count + (BitOperations.PopCount b.Values[i])
//            b.ValuesCount <- ValueSome count
            count

[<Struct>]
type Range =
    {
        Start : Index
        Length : Index
    }
    static member Zero =
        {
            Start = Index.create 0
            Length = Index.create 0
        }
    
module Range =
    
    let create start length =
        {
            Start = start
            Length = length
        }
    
    [<CompiledName("Iterate")>]
    let inline iter ([<InlineIfLambda>] f: Index -> unit) (range: Range) =
        let mutable i = range.Start
        let bound = range.Start + range.Length

        while i < bound do
            f i
            i <- i + LanguagePrimitives.Int32WithMeasure<Units.Index> 1
            
            
    let inline forall ([<InlineIfLambda>] f: Index -> bool) (range: Range) =
        let mutable result = true
        let mutable i = range.Start
        let bound = range.Start + range.Length

        while i < bound && result do
            result <- f i
            i <- i + LanguagePrimitives.Int32WithMeasure<Units.Index> 1
        
        result
            
    

type SourceRanges = Bar<Units.Node, Range>
type SourceEdges = Bar<Units.Index, Edge>
type TargetRanges = Bar<Units.Node, Range>
type TargetEdges = Bar<Units.Index, Edge>

[<Struct>]
type Graph = {
    SourceRanges : SourceRanges
    SourceEdges : SourceEdges
    TargetRanges : TargetRanges
    TargetEdges : TargetEdges
}
    
module Graph =
    
    let private getNodeCount (edges: Edge[]) =
        let nodes = HashSet()
        
        for edge in edges do
            let source = Edge.getSource edge
            let target = Edge.getTarget edge
            nodes.Add source |> ignore
            nodes.Add target |> ignore
            
        LanguagePrimitives.Int32WithMeasure<Units.Node> nodes.Count
    
    let private createSourcesAndTargets (nodeCount: int<Units.Node>) (edges: Edge[]) =
        let sourcesAcc = Row.create nodeCount []
        let targetsAcc = Row.create nodeCount []
        
        for edge in edges do
            let source = Edge.getSource edge
            let target = Edge.getTarget edge
            
            sourcesAcc[target] <- edge :: sourcesAcc[target]
            targetsAcc[source] <- edge :: targetsAcc[source]
            
        let finalSources =
            sourcesAcc
            |> Row.map Array.ofList
            
        let finalTargets =
            targetsAcc
            |> Row.map Array.ofList
            
        finalSources.Bar, finalTargets.Bar

        
    let private createIndexesAndValues (nodeData: Bar<'Measure, Edge[]>) =
        let ranges = Row.create nodeData.Length Range.Zero
        let mutable nextStartIndex = Index.create 0
        
        nodeData
        |> Bar.iteri (fun nodeId nodes ->
            let length =
                nodes.Length
                |> int
                |> Index.create
            let newRange = Range.create nextStartIndex length
            ranges[nodeId] <- newRange
            nextStartIndex <- nextStartIndex + length
            )
        
        let values =
            nodeData._Values
            |> Array.concat
            |> Bar<Units.Index, _>
        
        ranges.Bar, values
        
        
    let create (edges: Edge[]) =
        let nodeCount = getNodeCount edges
        let nodeSources, nodeTargets = createSourcesAndTargets nodeCount edges
        
        let sourceRanges, sourceNodes = createIndexesAndValues nodeSources
        let targetRanges, targetNodes = createIndexesAndValues nodeTargets
        
        {
            SourceRanges = sourceRanges
            SourceEdges = sourceNodes
            TargetRanges = targetRanges
            TargetEdges = targetNodes
        }        

    
    type GraphType() =
        static member inline AddToTracker(tracker: Span<uint64>,nodeCount:int, edge: Edge) =
            let source = Edge.getSource edge
            let target = Edge.getTarget edge
            let location = (int source) * nodeCount + (int target)
            
            let bucket = location >>> 6
            let offset = location &&& 0x3F
            let mask = 1UL <<< offset
            tracker[bucket] <- tracker[bucket] ||| mask
        
        static member inline RemoveFromTracker(tracker: Span<uint64>, nodeCount: int, edge: Edge) =
            let source = Edge.getSource edge
            let target = Edge.getTarget edge
            let location = (int source) * nodeCount + (int target)
            let bucket = location >>> 6
            let offset = location &&& 0x3F
            let mask = 1UL <<< offset
            tracker[bucket] <- tracker[bucket] &&& ~~~mask
        
        static member inline TrackerNotContains(tracker: Span<uint64>,nodeCount: int, edge: Edge) =
            let source = Edge.getSource edge
            let target = Edge.getTarget edge
            let location = (int source) * nodeCount + (int target)
            let bucket = location >>> 6
            let offset = location &&& 0x3F
            ((tracker[bucket] >>> offset) &&& 1UL) <> 1UL
        
        static member inline TrackerCount(tracker: Span<uint64>) =
            let mutable count = 0
            for i = 0 to tracker.Length - 1 do            
                count <- count + (BitOperations.PopCount tracker[i])
            count
        static member Sort(graph: inref<Graph>) =
            let sourceRanges = graph.SourceRanges
            let sourceEdges = graph.SourceEdges
            let targetRanges = graph.TargetRanges
            let targetEdges = graph.TargetEdges
            let sourceRangeLength = int sourceRanges.Length
            let result = GC.AllocateUninitializedArray (sourceRangeLength)
            let mutable nextToProcessIdx = 0
            let mutable resultCount = 0
            
            let mutable nodeId = 0<Units.Node>
            
            while nodeId < sourceRanges.Length do
                if sourceRanges[nodeId].Length = 0<Units.Index> then
                    result[resultCount] <- nodeId
                    resultCount <- resultCount + 1
                nodeId <- nodeId + 1<Units.Node>
            
            let bitsRequired = ((sourceRangeLength * sourceRangeLength) + 63) / 64
            let remainingEdges = (GC.AllocateUninitializedArray bitsRequired)
            let remainingEdgesSpan = remainingEdges.AsSpan()
//            printfn $"Edges count: {sourceEdges._Values.Length}, target edges: {targetEdges._Values.Length}"
//            remainingEdges.BatchAdd(Vector(sourceEdges._Values |> Array.stripUoM))
//            let parallelOptions = ParallelOptions(MaxDegreeOfParallelism = max (min Environment.ProcessorCount sourceEdges._Values.Length) 1)
//            Parallel.For(0, sourceEdges._Values.Length, parallelOptions, fun i ->
//                remainingEdges.Add(sourceEdges._Values[i])
//            ) |> ignore
//            sourceEdges._Values |> Array.Parallel.iter (fun edge -> remainingEdges.Add(edge))
//            sourceEdges._Values |> Array.Parallel.iter (fun edge -> GraphType.AddToTracker(remainingEdges, sourceRangeLength, edge))
//            
            for edge in sourceEdges._Values do
                GraphType.AddToTracker(remainingEdgesSpan, sourceRangeLength, edge)
//                remainingEdges.Add(edge)
            
            while nextToProcessIdx < result.Length && nextToProcessIdx < resultCount do

                let targetRange = targetRanges[result[nextToProcessIdx]]
                let mutable targetIndex = targetRange.Start
                let bound = targetRange.Start + targetRange.Length
                while targetIndex < bound do
                    GraphType.RemoveFromTracker(remainingEdgesSpan, sourceRangeLength, targetEdges[targetIndex])
//                    remainingEdges.Remove targetEdges[targetIndex]
            
                    // Check if all of the Edges have been removed for this
                    // Target Node
                    let targetNodeId = Edge.getTarget targetEdges[targetIndex]
                    
                    let mutable noRemainingSourcesResult = true
                    let range = sourceRanges[targetNodeId]
                    let mutable sourceIndex = range.Start
                    let bound = range.Start + range.Length

                    while sourceIndex < bound && noRemainingSourcesResult do
                        noRemainingSourcesResult <- GraphType.TrackerNotContains(remainingEdgesSpan, sourceRangeLength, sourceEdges[sourceIndex])
//                        noRemainingSourcesResult <- remainingEdges.NotContains sourceEdges[sourceIndex]
                        sourceIndex <- sourceIndex + LanguagePrimitives.Int32WithMeasure<Units.Index> 1
                                            
                    if noRemainingSourcesResult then
                        result[resultCount] <- targetNodeId
                        resultCount <- resultCount + 1

                    targetIndex <- targetIndex + 1<Units.Index>
                
                nextToProcessIdx <- nextToProcessIdx + 1


            if GraphType.TrackerCount(remainingEdges) > 0 then
                ValueNone
            else
                ValueSome result