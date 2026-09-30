// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace Microsoft.FSharp.Collections

open System
open System.Collections.Generic
open System.Collections
open System.Diagnostics
open System.Runtime.CompilerServices
open System.Text
open Microsoft.FSharp.Core
open Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators

/// The representation a <see cref="T:Microsoft.FSharp.Collections.MapNode`2"/> uses for its entries.
type internal MapNodeKind =
    /// Entries and sub-nodes indexed by bitmaps of hash fragments.
    | Bitmap = 0
    /// Entries sharing one full hash, reached once all hash bits are consumed.
    | Collision = 1
    /// A few entries in key order, with no sub-nodes; the root of a small map.
    | Flat = 2

/// A node of a CHAMP (Compressed Hash-Array Mapped Prefix-tree) keyed by the structural hash of the key.
///
/// A bitmap node stores the entries whose hash fragment at its level is set in <c>DataMap</c>, in bit
/// order, and the sub-nodes whose fragment is set in <c>NodeMap</c>, also in bit order. A collision node,
/// reached once all 32 hash bits are consumed, stores every entry that shares <c>CollisionHash</c>.
///
/// Every node below the root holds at least two entries, counting those of its sub-nodes; a sub-node
/// left with a single entry is inlined into its parent. The shape of a trie is therefore a function of
/// its contents alone.
///
/// A map of at most <c>MapNode.MaxFlat</c> entries built by insertion uses a single flat node instead:
/// its entries are kept in key order, so lookup is a short comparison scan, and ordered traversal needs
/// no sort. The flat node only ever appears as the root. Once a ninth entry arrives the entries move
/// into a trie, and a trie does not turn back into a flat node when it shrinks.
[<NoEquality; NoComparison>]
[<Sealed>]
[<AllowNullLiteral>]
type internal MapNode<'Key, 'Value>
    (
        dataMap: uint32,
        nodeMap: uint32,
        entries: KeyValuePair<'Key, 'Value>[],
        nodes: MapNode<'Key, 'Value>[],
        collisionHash: int,
        kind: MapNodeKind
    ) =
    member _.DataMap = dataMap
    member _.NodeMap = nodeMap
    member _.Entries = entries
    member _.Nodes = nodes
    member _.CollisionHash = collisionHash
    member _.Kind = kind

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module MapNode =

    /// The number of hash bits consumed by each level of the trie.
    [<Literal>]
    let private BitsPerLevel = 5

    /// The shift at which the hash is exhausted and entries fall into collision nodes.
    [<Literal>]
    let private HashExhausted = 32

    /// The largest number of entries kept in a flat root.
    [<Literal>]
    let MaxFlat = 8

    let empty = null

#if NET
    let inline private popCount (x: uint32) =
        System.Numerics.BitOperations.PopCount x
#else
    let inline private popCount (x: uint32) =
        let x = x - ((x >>> 1) &&& 0x55555555u)
        let x = (x &&& 0x33333333u) + ((x >>> 2) &&& 0x33333333u)
        let x = (x + (x >>> 4)) &&& 0x0F0F0F0Fu
        int ((x * 0x01010101u) >>> 24)
#endif

    let inline private bitpos (h: int) (shift: int) =
        1u <<< int ((uint32 h >>> shift) &&& 31u)

    let inline private index (bitmap: uint32) (bit: uint32) =
        popCount (bitmap &&& (bit - 1u))

    let inline private isSingleton (m: MapNode<'Key, 'Value>) =
        m.Nodes.Length = 0 && m.Entries.Length = 1

    let private bitmapNode dataMap nodeMap entries nodes =
        MapNode<'Key, 'Value>(dataMap, nodeMap, entries, nodes, 0, MapNodeKind.Bitmap)

    let private collisionNode h entries =
        MapNode<'Key, 'Value>(0u, 0u, entries, Array.empty, h, MapNodeKind.Collision)

    let private flatNode entries =
        MapNode<'Key, 'Value>(0u, 0u, entries, Array.empty, 0, MapNodeKind.Flat)

    let private insertAt (arr: 'T[]) (i: int) (x: 'T) : 'T[] =
        let res = Array.zeroCreate (arr.Length + 1)
        Array.blit arr 0 res 0 i
        res[i] <- x
        Array.blit arr i res (i + 1) (arr.Length - i)
        res

    let private removeAt (arr: 'T[]) (i: int) : 'T[] =
        let res = Array.zeroCreate (arr.Length - 1)
        Array.blit arr 0 res 0 i
        Array.blit arr (i + 1) res i (arr.Length - i - 1)
        res

    let private setAt (arr: 'T[]) (i: int) (x: 'T) : 'T[] =
        let res = Array.copy arr
        res[i] <- x
        res

    let private indexOfKey (comparer: IComparer<'Key>) (k: 'Key) (entries: KeyValuePair<'Key, 'Value>[]) =
        let mutable i = 0

        while i < entries.Length && comparer.Compare(k, entries[i].Key) <> 0 do
            i <- i + 1

        if i < entries.Length then i else -1

    /// The index of <c>k</c> in key-ordered <c>entries</c>, or the bitwise complement of the index at
    /// which it would be inserted. A binary search: at most four comparisons for a full flat root.
    let private flatIndexOf (comparer: IComparer<'Key>) (k: 'Key) (entries: KeyValuePair<'Key, 'Value>[]) =
        let mutable lo = 0
        let mutable hi = entries.Length - 1
        let mutable res = -1

        while res < 0 && lo <= hi do
            let mid = (lo + hi) >>> 1
            let c = comparer.Compare(k, entries[mid].Key)

            if c = 0 then res <- mid
            elif c < 0 then hi <- mid - 1
            else lo <- mid + 1

        if res >= 0 then res else ~~~lo

    let tryGetValue (comparer: IComparer<'Key>) (k: 'Key) (v: byref<'Value>) (m: MapNode<'Key, 'Value>) =
        if isNull m then
            false
        elif m.Kind = MapNodeKind.Flat then
            let i = flatIndexOf comparer k m.Entries

            if i >= 0 then
                v <- m.Entries[i].Value
                true
            else
                false
        else

            let h = Unchecked.hash k
            let mutable node = m
            let mutable shift = 0
            let mutable found = false
            let mutable searching = true

            while searching do
                if node.Kind = MapNodeKind.Collision then
                    let i = indexOfKey comparer k node.Entries

                    if i >= 0 then
                        v <- node.Entries[i].Value
                        found <- true

                    searching <- false
                else
                    let bit = bitpos h shift

                    if node.DataMap &&& bit <> 0u then
                        let e = node.Entries[index node.DataMap bit]

                        if comparer.Compare(k, e.Key) = 0 then
                            v <- e.Value
                            found <- true

                        searching <- false
                    elif node.NodeMap &&& bit <> 0u then
                        node <- node.Nodes[index node.NodeMap bit]
                        shift <- shift + BitsPerLevel
                    else
                        searching <- false

            found

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let throwKeyNotFound () =
        raise (KeyNotFoundException())

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let find (comparer: IComparer<'Key>) k (m: MapNode<'Key, 'Value>) =
        let mutable v = Unchecked.defaultof<'Value>

        if tryGetValue comparer k &v m then
            v
        else
            throwKeyNotFound ()

    let tryFind (comparer: IComparer<'Key>) k (m: MapNode<'Key, 'Value>) =
        let mutable v = Unchecked.defaultof<'Value>

        if tryGetValue comparer k &v m then
            Some v
        else
            None

    let mem (comparer: IComparer<'Key>) k (m: MapNode<'Key, 'Value>) =
        let mutable v = Unchecked.defaultof<'Value>
        tryGetValue comparer k &v m

    /// Builds the smallest sub-trie holding two entries with distinct keys.
    let rec private mergeTwo
        (h1: int)
        (e1: KeyValuePair<'Key, 'Value>)
        (h2: int)
        (e2: KeyValuePair<'Key, 'Value>)
        shift
        =
        if shift >= HashExhausted then
            collisionNode h1 [| e1; e2 |]
        else
            let bit1 = bitpos h1 shift
            let bit2 = bitpos h2 shift

            if bit1 = bit2 then
                bitmapNode 0u bit1 Array.empty [| mergeTwo h1 e1 h2 e2 (shift + BitsPerLevel) |]
            elif bit1 < bit2 then
                bitmapNode (bit1 ||| bit2) 0u [| e1; e2 |] Array.empty
            else
                bitmapNode (bit1 ||| bit2) 0u [| e2; e1 |] Array.empty

    /// Adds or replaces the entry for <c>k</c>. Sets <c>replaced</c> when the key was already present.
    let rec private addAux
        (comparer: IComparer<'Key>)
        (h: int)
        (k: 'Key)
        (v: 'Value)
        shift
        (m: MapNode<'Key, 'Value>)
        (replaced: byref<bool>)
        : MapNode<'Key, 'Value> =
        if isNull m then
            bitmapNode (bitpos h shift) 0u [| KeyValuePair(k, v) |] Array.empty
        elif m.Kind = MapNodeKind.Collision then
            let i = indexOfKey comparer k m.Entries

            if i >= 0 then
                replaced <- true
                collisionNode h (setAt m.Entries i (KeyValuePair(k, v)))
            else
                collisionNode h (insertAt m.Entries m.Entries.Length (KeyValuePair(k, v)))
        else
            let bit = bitpos h shift

            if m.DataMap &&& bit <> 0u then
                let idx = index m.DataMap bit
                let e = m.Entries[idx]

                if comparer.Compare(k, e.Key) = 0 then
                    replaced <- true
                    bitmapNode m.DataMap m.NodeMap (setAt m.Entries idx (KeyValuePair(k, v))) m.Nodes
                else
                    let sub =
                        mergeTwo (Unchecked.hash e.Key) e h (KeyValuePair(k, v)) (shift + BitsPerLevel)

                    let nidx = index m.NodeMap bit

                    bitmapNode
                        (m.DataMap ^^^ bit)
                        (m.NodeMap ||| bit)
                        (removeAt m.Entries idx)
                        (insertAt m.Nodes nidx sub)
            elif m.NodeMap &&& bit <> 0u then
                let nidx = index m.NodeMap bit
                let sub = addAux comparer h k v (shift + BitsPerLevel) m.Nodes[nidx] &replaced
                bitmapNode m.DataMap m.NodeMap m.Entries (setAt m.Nodes nidx sub)
            else
                let idx = index m.DataMap bit
                bitmapNode (m.DataMap ||| bit) m.NodeMap (insertAt m.Entries idx (KeyValuePair(k, v))) m.Nodes

    /// Moves the entries of a full flat root into a trie and adds one more, whose key is not among them.
    let private flatToTrie (comparer: IComparer<'Key>) (entries: KeyValuePair<'Key, 'Value>[]) (k: 'Key) (v: 'Value) =
        let mutable t: MapNode<'Key, 'Value> = null
        let mutable replaced = false

        for e in entries do
            t <- addAux comparer (Unchecked.hash e.Key) e.Key e.Value 0 t &replaced

        addAux comparer (Unchecked.hash k) k v 0 t &replaced

    let add (comparer: IComparer<'Key>) (k: 'Key) (v: 'Value) (m: MapNode<'Key, 'Value>) (replaced: byref<bool>) =
        if isNull m then
            flatNode [| KeyValuePair(k, v) |]
        elif m.Kind = MapNodeKind.Flat then
            let i = flatIndexOf comparer k m.Entries

            if i >= 0 then
                replaced <- true
                flatNode (setAt m.Entries i (KeyValuePair(k, v)))
            elif m.Entries.Length < MaxFlat then
                flatNode (insertAt m.Entries (~~~i) (KeyValuePair(k, v)))
            else
                flatToTrie comparer m.Entries k v
        else
            addAux comparer (Unchecked.hash k) k v 0 m &replaced

    /// Removes the entry for <c>k</c>, returning <c>m</c> itself when the key is absent. Sets <c>removed</c>
    /// when an entry was removed. The result may be a singleton, which a parent must inline, or null.
    let rec private removeAux
        (comparer: IComparer<'Key>)
        (h: int)
        (k: 'Key)
        shift
        (m: MapNode<'Key, 'Value>)
        (removed: byref<bool>)
        : MapNode<'Key, 'Value> =
        if isNull m then
            m
        elif m.Kind = MapNodeKind.Collision then
            let i = indexOfKey comparer k m.Entries

            if i < 0 then
                m
            else
                removed <- true
                collisionNode h (removeAt m.Entries i)
        else
            let bit = bitpos h shift

            if m.DataMap &&& bit <> 0u then
                let idx = index m.DataMap bit

                if comparer.Compare(k, m.Entries[idx].Key) <> 0 then
                    m
                else
                    removed <- true

                    if m.Entries.Length = 1 && m.Nodes.Length = 0 then
                        null
                    else
                        bitmapNode (m.DataMap ^^^ bit) m.NodeMap (removeAt m.Entries idx) m.Nodes
            elif m.NodeMap &&& bit <> 0u then
                let nidx = index m.NodeMap bit
                let sub = removeAux comparer h k (shift + BitsPerLevel) m.Nodes[nidx] &removed

                if not removed then
                    m
                elif isNull sub then
                    bitmapNode m.DataMap (m.NodeMap ^^^ bit) m.Entries (removeAt m.Nodes nidx)
                elif isSingleton sub then
                    let idx = index m.DataMap bit

                    bitmapNode
                        (m.DataMap ||| bit)
                        (m.NodeMap ^^^ bit)
                        (insertAt m.Entries idx sub.Entries[0])
                        (removeAt m.Nodes nidx)
                else
                    bitmapNode m.DataMap m.NodeMap m.Entries (setAt m.Nodes nidx sub)
            else
                m

    let remove (comparer: IComparer<'Key>) (k: 'Key) (m: MapNode<'Key, 'Value>) (removed: byref<bool>) =
        if isNull m then
            m
        elif m.Kind = MapNodeKind.Flat then
            let i = flatIndexOf comparer k m.Entries

            if i < 0 then
                m
            else
                removed <- true

                if m.Entries.Length = 1 then
                    null
                else
                    flatNode (removeAt m.Entries i)
        else
            removeAux comparer (Unchecked.hash k) k 0 m &removed

    /// Adds every pair in turn, returning the root and the number of distinct keys.
    let ofSeq (comparer: IComparer<'Key>) (elements: seq<'Key * 'Value>) =
        let mutable root: MapNode<'Key, 'Value> = null
        let mutable count = 0
        use e = elements.GetEnumerator()

        while e.MoveNext() do
            let (k, v) = e.Current
            let mutable replaced = false
            root <- add comparer k v root &replaced

            if not replaced then
                count <- count + 1

        struct (root, count)

    let rec private existsAux (f: OptimizedClosures.FSharpFunc<_, _, _>) (m: MapNode<'Key, 'Value>) =
        let mutable res = false
        let mutable i = 0

        while not res && i < m.Entries.Length do
            let e = m.Entries[i]
            res <- f.Invoke(e.Key, e.Value)
            i <- i + 1

        i <- 0

        while not res && i < m.Nodes.Length do
            res <- existsAux f m.Nodes[i]
            i <- i + 1

        res

    /// Tests the entries in trie order, which is not key order.
    let existsUnordered f (m: MapNode<'Key, 'Value>) =
        (not (isNull m)) && existsAux (OptimizedClosures.FSharpFunc<_, _, _>.Adapt f) m

    let rec private fillArray (arr: KeyValuePair<'Key, 'Value>[]) (i: int) (m: MapNode<'Key, 'Value>) =
        Array.blit m.Entries 0 arr i m.Entries.Length
        let mutable i = i + m.Entries.Length

        for n in m.Nodes do
            i <- fillArray arr i n

        i

    /// The entries in trie order: those of a node first, then those of its sub-nodes in turn.
    let toEntries (count: int) (m: MapNode<'Key, 'Value>) =
        let arr = Array.zeroCreate count

        if not (isNull m) then
            fillArray arr 0 m |> ignore

        arr

    let rec private extremumAux
        (comparer: IComparer<'Key>)
        (wantMax: bool)
        (best: byref<KeyValuePair<'Key, 'Value>>)
        (hasBest: byref<bool>)
        (m: MapNode<'Key, 'Value>)
        =
        for e in m.Entries do
            if not hasBest then
                best <- e
                hasBest <- true
            else
                let c = comparer.Compare(e.Key, best.Key)

                if (if wantMax then c > 0 else c < 0) then
                    best <- e

        for n in m.Nodes do
            extremumAux comparer wantMax &best &hasBest n

    /// The entry with the least (or, with <c>wantMax</c>, the greatest) key, by a scan of the trie.
    let extremum (comparer: IComparer<'Key>) (wantMax: bool) (m: MapNode<'Key, 'Value>) =
        let mutable best = Unchecked.defaultof<KeyValuePair<'Key, 'Value>>
        let mutable hasBest = false

        if not (isNull m) then
            extremumAux comparer wantMax &best &hasBest m

        if hasBest then
            (best.Key, best.Value)
        else
            throwKeyNotFound ()

    let rec private mapFromArrayAux (values: 'Result[]) (pos: byref<int>) (m: MapNode<'Key, 'Value>) =
        let entries = Array.zeroCreate m.Entries.Length

        for i in 0 .. entries.Length - 1 do
            entries[i] <- KeyValuePair(m.Entries[i].Key, values[pos])
            pos <- pos + 1

        let nodes = Array.zeroCreate m.Nodes.Length

        for i in 0 .. nodes.Length - 1 do
            nodes[i] <- mapFromArrayAux values &pos m.Nodes[i]

        MapNode<'Key, 'Result>(m.DataMap, m.NodeMap, entries, nodes, m.CollisionHash, m.Kind)

    /// Rebuilds the trie with the same shape, taking each entry's new value from <c>values</c> in trie order.
    let mapFromArray (values: 'Result[]) (m: MapNode<'Key, 'Value>) =
        if isNull m then
            null
        else
            let mutable pos = 0
            mapFromArrayAux values &pos m

    let rec private filterFromMaskAux (keep: bool[]) (sense: bool) (pos: byref<int>) (m: MapNode<'Key, 'Value>) =
        let start = pos
        pos <- pos + m.Entries.Length

        if m.Kind <> MapNodeKind.Bitmap then
            let mutable n = 0

            for i in 0 .. m.Entries.Length - 1 do
                if keep[start + i] = sense then
                    n <- n + 1

            if n = m.Entries.Length then
                m
            elif n = 0 then
                null
            else
                let entries = Array.zeroCreate n
                let mutable j = 0

                for i in 0 .. m.Entries.Length - 1 do
                    if keep[start + i] = sense then
                        entries[j] <- m.Entries[i]
                        j <- j + 1

                MapNode<'Key, 'Value>(0u, 0u, entries, Array.empty, m.CollisionHash, m.Kind)
        else
            let subs = Array.zeroCreate m.Nodes.Length

            for i in 0 .. subs.Length - 1 do
                subs[i] <- filterFromMaskAux keep sense &pos m.Nodes[i]

            let entries = Array.zeroCreate (m.Entries.Length + subs.Length)
            let nodes = Array.zeroCreate subs.Length
            let mutable dataMap = 0u
            let mutable nodeMap = 0u
            let mutable ne = 0
            let mutable nn = 0
            let mutable di = 0
            let mutable ni = 0
            let mutable changed = false

            for b in 0..31 do
                let bit = 1u <<< b

                if m.DataMap &&& bit <> 0u then
                    if keep[start + di] = sense then
                        entries[ne] <- m.Entries[di]
                        ne <- ne + 1
                        dataMap <- dataMap ||| bit
                    else
                        changed <- true

                    di <- di + 1
                elif m.NodeMap &&& bit <> 0u then
                    let sub = subs[ni]

                    if isNull sub then
                        changed <- true
                    elif isSingleton sub then
                        entries[ne] <- sub.Entries[0]
                        ne <- ne + 1
                        dataMap <- dataMap ||| bit
                        changed <- true
                    else
                        nodes[nn] <- sub
                        nn <- nn + 1
                        nodeMap <- nodeMap ||| bit

                        if not (obj.ReferenceEquals(sub, m.Nodes[ni])) then
                            changed <- true

                    ni <- ni + 1

            if not changed then
                m
            elif ne = 0 && nn = 0 then
                null
            else
                let entries =
                    if ne = entries.Length then
                        entries
                    else
                        Array.sub entries 0 ne

                let nodes =
                    if nn = nodes.Length then
                        nodes
                    else
                        Array.sub nodes 0 nn

                bitmapNode dataMap nodeMap entries nodes

    /// Keeps the entries whose flag in <c>keep</c>, indexed in trie order, equals <c>sense</c>.
    let filterFromMask (keep: bool[]) (sense: bool) (m: MapNode<'Key, 'Value>) =
        if isNull m then
            null
        else
            let mutable pos = 0
            filterFromMaskAux keep sense &pos m

    let notStarted () =
        raise (InvalidOperationException(SR.GetString(SR.enumerationNotStarted)))

    let alreadyFinished () =
        raise (InvalidOperationException(SR.GetString(SR.enumerationAlreadyFinished)))

/// The entries of a map in key order, with the trie-order position of each, computed once per map instance.
[<NoEquality; NoComparison>]
[<Sealed>]
[<AllowNullLiteral>]
type internal MapSortedView<'Key, 'Value>(sorted: KeyValuePair<'Key, 'Value>[], order: int[]) =
    /// The entries in key order.
    member _.Sorted = sorted
    /// <c>Order[i]</c> is the trie-order position of <c>Sorted[i]</c>.
    member _.Order = order

[<Sealed>]
type internal MapEnumerator<'Key, 'Value>(entries: KeyValuePair<'Key, 'Value>[]) =
    let mutable index = -1

    member _.Current =
        if index < 0 then
            MapNode.notStarted ()
        elif index >= entries.Length then
            MapNode.alreadyFinished ()
        else
            entries[index]

    interface IEnumerator<KeyValuePair<'Key, 'Value>> with
        member this.Current = this.Current

    interface IEnumerator with
        member this.Current = box this.Current

        member _.MoveNext() =
            if index < entries.Length then
                index <- index + 1

            index < entries.Length

        member _.Reset() =
            index <- -1

    interface IDisposable with
        member _.Dispose() =
            ()

[<DebuggerTypeProxy(typedefof<MapDebugView<_, _>>)>]
[<DebuggerDisplay("Count = {Count}")>]
[<Sealed>]
[<CompiledName("FSharpMap`2")>]
type Map<[<EqualityConditionalOn>] 'Key, [<EqualityConditionalOn; ComparisonConditionalOn>] 'Value when 'Key: comparison>
    (comparer: IComparer<'Key>, root: MapNode<'Key, 'Value>, count: int) =

    [<NonSerialized>]
    // This type is logically immutable. This field is only mutated during deserialization.
    let mutable comparer = comparer

    [<NonSerialized>]
    // This type is logically immutable. This field is only mutated during deserialization.
    let mutable root = root

    [<NonSerialized>]
    // This type is logically immutable. This field is only mutated during deserialization.
    let mutable count = count

    [<NonSerialized>]
    // The entries in key order, computed by the first operation that observes key order and then shared.
    // Concurrent first observers each compute an identical view; publishing either is harmless.
    let mutable sortedView: MapSortedView<'Key, 'Value> = null

    // This type is logically immutable. This field is only mutated during serialization and deserialization.
    //
    // WARNING: The compiled name of this field may never be changed because it is part of the logical
    // WARNING: permanent serialization format for this type.
    let mutable serializedData = null

    // We use .NET generics per-instantiation static fields to avoid allocating a new object for each empty
    // set (it is just a lookup into a .NET table of type-instantiation-indexed static fields).
    static let empty =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        new Map<'Key, 'Value>(comparer, MapNode.empty, 0)

    // Orders entries by key with the same comparer every instance uses.
    static let entryComparer =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>

        { new IComparer<KeyValuePair<'Key, 'Value>> with
            member _.Compare(a, b) =
                comparer.Compare(a.Key, b.Key)
        }

    [<System.Runtime.Serialization.OnSerializingAttribute>]
    member m.OnSerializing(context: System.Runtime.Serialization.StreamingContext) =
        ignore context
        serializedData <- m.SortedEntries

    // Do not set this to null, since concurrent threads may also be serializing the data
    //[<System.Runtime.Serialization.OnSerializedAttribute>]
    //member _.OnSerialized(context: System.Runtime.Serialization.StreamingContext) =
    //    serializedData <- null

    [<System.Runtime.Serialization.OnDeserializedAttribute>]
    member _.OnDeserialized(context: System.Runtime.Serialization.StreamingContext) =
        ignore context
        comparer <- LanguagePrimitives.FastGenericComparer<'Key>

        let struct (newRoot, newCount) =
            MapNode.ofSeq comparer (serializedData |> Array.map (fun kvp -> kvp.Key, kvp.Value))

        root <- newRoot
        count <- newCount
        sortedView <- null
        serializedData <- null

    static member Empty: Map<'Key, 'Value> = empty

    static member Create(ie: IEnumerable<_>) : Map<'Key, 'Value> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let struct (root, count) = MapNode.ofSeq comparer ie
        Map<_, _>(comparer, root, count)

    new(elements: seq<_>) =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let struct (root, count) = MapNode.ofSeq comparer elements
        Map<_, _>(comparer, root, count)

    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member internal m.Comparer = comparer

    /// The entries in key order together with their trie-order positions. Computed on first use.
    member internal m.SortedView =
        match sortedView with
        | null ->
            let entries = MapNode.toEntries count root
            let order = Array.zeroCreate count

            for i in 0 .. count - 1 do
                order[i] <- i

            Array.Sort<KeyValuePair<'Key, 'Value>, int>(entries, order, entryComparer)
            let view = MapSortedView(entries, order)
            sortedView <- view
            view
        | view -> view

    /// The entries in key order, and their trie-order positions when trie order differs from key order.
    member private m.OrderedEntries: struct (KeyValuePair<'Key, 'Value>[] * int[]) =
        if root.Kind = MapNodeKind.Flat then
            struct (root.Entries, null)
        else
            let view = m.SortedView
            struct (view.Sorted, view.Order)

    /// The entries in key order.
    member internal m.SortedEntries: KeyValuePair<'Key, 'Value>[] =
        if count = 0 then
            Array.empty
        elif root.Kind = MapNodeKind.Flat then
            root.Entries
        else
            m.SortedView.Sorted

    member m.Add(key, value) : Map<'Key, 'Value> =
        let mutable replaced = false
        let newRoot = MapNode.add comparer key value root &replaced
        new Map<'Key, 'Value>(comparer, newRoot, (if replaced then count else count + 1))

    member m.Change(key, f: 'Value option -> 'Value option) : Map<'Key, 'Value> =
        let existing = MapNode.tryFind comparer key root

        match f existing with
        | Some value -> m.Add(key, value)
        | None ->
            match existing with
            | Some _ -> m.Remove key
            | None -> m

    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member m.IsEmpty = count = 0

    member m.Item
        with get (key: 'Key) = MapNode.find comparer key root

    member m.TryPick(f: 'Key -> 'Value -> 'T option) =
        let entries = m.SortedEntries
        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt f
        let mutable res = None
        let mutable i = 0

        while res.IsNone && i < entries.Length do
            let e = entries[i]
            res <- f.Invoke(e.Key, e.Value)
            i <- i + 1

        res

    member m.Exists(predicate: 'Key -> 'Value -> bool) =
        let entries = m.SortedEntries
        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt predicate
        let mutable res = false
        let mutable i = 0

        while not res && i < entries.Length do
            let e = entries[i]
            res <- f.Invoke(e.Key, e.Value)
            i <- i + 1

        res

    member m.ForAll(predicate: 'Key -> 'Value -> bool) =
        let entries = m.SortedEntries
        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt predicate
        let mutable res = true
        let mutable i = 0

        while res && i < entries.Length do
            let e = entries[i]
            res <- f.Invoke(e.Key, e.Value)
            i <- i + 1

        res

    member internal m.ContainsValue(value: 'Value) =
        MapNode.existsUnordered (fun _ v -> Unchecked.equals v value) root

    /// Evaluates <c>predicate</c> on every entry in key order and returns the flags indexed in trie order,
    /// with the number of entries that passed.
    member private m.KeepMask(predicate: 'Key -> 'Value -> bool) =
        let struct (sorted, order) = m.OrderedEntries
        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt predicate
        let keep = Array.zeroCreate count
        let mutable kept = 0

        for i in 0 .. count - 1 do
            let e = sorted[i]
            let b = f.Invoke(e.Key, e.Value)

            match order with
            | null -> keep[i] <- b
            | order -> keep[order[i]] <- b

            if b then
                kept <- kept + 1

        struct (keep, kept)

    member m.Filter(predicate: 'Key -> 'Value -> bool) =
        if count = 0 then
            m
        else
            let struct (keep, kept) = m.KeepMask predicate

            if kept = count then
                m
            elif kept = 0 then
                empty
            else
                new Map<'Key, 'Value>(comparer, MapNode.filterFromMask keep true root, kept)

    member m.Partition(predicate: 'Key -> 'Value -> bool) : Map<'Key, 'Value> * Map<'Key, 'Value> =
        if count = 0 then
            m, m
        else
            let struct (keep, kept) = m.KeepMask predicate

            if kept = count then
                m, empty
            elif kept = 0 then
                empty, m
            else
                new Map<'Key, 'Value>(comparer, MapNode.filterFromMask keep true root, kept),
                new Map<'Key, 'Value>(comparer, MapNode.filterFromMask keep false root, count - kept)

    member m.Iterate(f: 'Key -> 'Value -> unit) =
        let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt f

        for e in m.SortedEntries do
            f.Invoke(e.Key, e.Value)

    member m.Map(f: 'Key -> 'Value -> 'Result) : Map<'Key, 'Result> =
        if count = 0 then
            Map<'Key, 'Result>.Empty
        else
            let struct (sorted, order) = m.OrderedEntries
            let f = OptimizedClosures.FSharpFunc<_, _, _>.Adapt f
            let values = Array.zeroCreate count

            for i in 0 .. count - 1 do
                let e = sorted[i]

                match order with
                | null -> values[i] <- f.Invoke(e.Key, e.Value)
                | order -> values[order[i]] <- f.Invoke(e.Key, e.Value)

            new Map<'Key, 'Result>(comparer, MapNode.mapFromArray values root, count)

    member m.Count = count

    member m.ContainsKey key =
        MapNode.mem comparer key root

    member m.Remove key =
        let mutable removed = false
        let newRoot = MapNode.remove comparer key root &removed

        if removed then
            new Map<'Key, 'Value>(comparer, newRoot, count - 1)
        else
            m

    member m.TryGetValue(key, [<System.Runtime.InteropServices.Out>] value: byref<'Value>) =
        MapNode.tryGetValue comparer key &value root

    member m.TryFind key =
        MapNode.tryFind comparer key root

    member m.ToList() =
        let entries = m.SortedEntries
        let mutable acc = []

        for i = entries.Length - 1 downto 0 do
            let e = entries[i]
            acc <- (e.Key, e.Value) :: acc

        acc

    member m.ToArray() =
        let entries = m.SortedEntries
        let res = Array.zeroCreate entries.Length

        for i in 0 .. entries.Length - 1 do
            let e = entries[i]
            res[i] <- (e.Key, e.Value)

        res

    member m.Keys = KeyCollection(m) :> ICollection<'Key>

    member m.Values = ValueCollection(m) :> ICollection<'Value>

    member m.MinKeyValue =
        if count = 0 then
            MapNode.throwKeyNotFound ()

        if root.Kind = MapNodeKind.Flat then
            let e = root.Entries[0]
            (e.Key, e.Value)
        else
            match sortedView with
            | null -> MapNode.extremum comparer false root
            | view ->
                let e = view.Sorted[0]
                (e.Key, e.Value)

    member m.MaxKeyValue =
        if count = 0 then
            MapNode.throwKeyNotFound ()

        if root.Kind = MapNodeKind.Flat then
            let e = root.Entries[root.Entries.Length - 1]
            (e.Key, e.Value)
        else
            match sortedView with
            | null -> MapNode.extremum comparer true root
            | view ->
                let e = view.Sorted[view.Sorted.Length - 1]
                (e.Key, e.Value)

    static member ofList l : Map<'Key, 'Value> =
        let comparer = LanguagePrimitives.FastGenericComparer<'Key>
        let struct (root, count) = MapNode.ofSeq comparer l
        Map<_, _>(comparer, root, count)

    member this.ComputeHashCode() =
        let combineHash x y =
            (x <<< 1) + y + 631

        let mutable res = 0

        for KeyValue(x, y) in this do
            res <- combineHash res (hash x)
            res <- combineHash res (Unchecked.hash y)

        res

    override this.Equals that =
        match that with
        | :? Map<'Key, 'Value> as that ->
            count = that.Count
            && (let e1 = this.SortedEntries
                let e2 = that.SortedEntries
                let mutable eq = true
                let mutable i = 0

                while eq && i < e1.Length do
                    let e1c = e1[i]
                    let e2c = e2[i]
                    eq <- (e1c.Key = e2c.Key) && Unchecked.equals e1c.Value e2c.Value
                    i <- i + 1

                eq)
        | _ -> false

    override this.GetHashCode() =
        this.ComputeHashCode()

    interface IStructuralEquatable with
        member this.Equals(that, comparer) =
            match that with
            | :? Map<'Key, 'Value> as that ->
                count = that.Count
                && (let e1 = this.SortedEntries
                    let e2 = that.SortedEntries
                    let mutable eq = true
                    let mutable i = 0

                    while eq && i < e1.Length do
                        let e1c = e1[i]
                        let e2c = e2[i]
                        eq <- comparer.Equals(e1c.Key, e2c.Key) && comparer.Equals(e1c.Value, e2c.Value)
                        i <- i + 1

                    eq)
            | _ -> false

        member this.GetHashCode(comparer) =
            let combineHash x y =
                (x <<< 1) + y + 631

            let mutable res = 0

            for KeyValue(x, y) in this do
                res <- combineHash res (comparer.GetHashCode x)
                res <- combineHash res (comparer.GetHashCode y)

            res

    interface IEnumerable<KeyValuePair<'Key, 'Value>> with
        member m.GetEnumerator() =
            new MapEnumerator<'Key, 'Value>(m.SortedEntries) :> IEnumerator<KeyValuePair<'Key, 'Value>>

    interface IEnumerable with
        member m.GetEnumerator() =
            new MapEnumerator<'Key, 'Value>(m.SortedEntries) :> IEnumerator

    interface IDictionary<'Key, 'Value> with
        member m.Item
            with get x = m.[x]
            and set _ _ = raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member m.Keys = m.Keys

        member m.Values = m.Values

        member m.Add(_, _) =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member m.ContainsKey k =
            m.ContainsKey k

        member m.TryGetValue(k, r) =
            m.TryGetValue(k, &r)

        member m.Remove _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

    interface ICollection<KeyValuePair<'Key, 'Value>> with
        member _.Add _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Clear() =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Remove _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member m.Contains x =
            let mutable v = Unchecked.defaultof<'Value>
            m.TryGetValue(x.Key, &v) && Unchecked.equals v x.Value

        member m.CopyTo(arr, i) =
            let entries = m.SortedEntries
            Array.blit entries 0 arr i entries.Length

        member _.IsReadOnly = true

        member m.Count = m.Count

    interface IComparable with
        member m.CompareTo(obj: objnull) =
            match obj with
            | :? Map<'Key, 'Value> as m2 ->
                Seq.compareWith
                    (fun (kvp1: KeyValuePair<_, _>) (kvp2: KeyValuePair<_, _>) ->
                        let c = comparer.Compare(kvp1.Key, kvp2.Key) in

                        if c <> 0 then
                            c
                        else
                            Unchecked.compare kvp1.Value kvp2.Value)
                    m
                    m2
            | _ -> invalidArg "obj" (SR.GetString(SR.notComparable))

    interface IReadOnlyCollection<KeyValuePair<'Key, 'Value>> with
        member m.Count = m.Count

    interface IReadOnlyDictionary<'Key, 'Value> with

        member m.Item
            with get key = m.[key]

        member m.Keys = m.Keys :> IEnumerable<'Key>

        member m.TryGetValue(key, value: byref<'Value>) =
            m.TryGetValue(key, &value)

        member m.Values = m.Values :> IEnumerable<'Value>

        member m.ContainsKey key =
            m.ContainsKey key

    override x.ToString() =
        match List.ofSeq (Seq.truncate 4 x) with
        | [] -> "map []"
        | [ KeyValue h1 ] ->
            let txt1 = LanguagePrimitives.anyToStringShowingNull h1
            StringBuilder().Append("map [").Append(txt1).Append("]").ToString()
        | [ KeyValue h1; KeyValue h2 ] ->
            let txt1 = LanguagePrimitives.anyToStringShowingNull h1
            let txt2 = LanguagePrimitives.anyToStringShowingNull h2

            StringBuilder().Append("map [").Append(txt1).Append("; ").Append(txt2).Append("]").ToString()
        | [ KeyValue h1; KeyValue h2; KeyValue h3 ] ->
            let txt1 = LanguagePrimitives.anyToStringShowingNull h1
            let txt2 = LanguagePrimitives.anyToStringShowingNull h2
            let txt3 = LanguagePrimitives.anyToStringShowingNull h3

            StringBuilder()
                .Append("map [")
                .Append(txt1)
                .Append("; ")
                .Append(txt2)
                .Append("; ")
                .Append(txt3)
                .Append("]")
                .ToString()
        | KeyValue h1 :: KeyValue h2 :: KeyValue h3 :: _ ->
            let txt1 = LanguagePrimitives.anyToStringShowingNull h1
            let txt2 = LanguagePrimitives.anyToStringShowingNull h2
            let txt3 = LanguagePrimitives.anyToStringShowingNull h3

            StringBuilder()
                .Append("map [")
                .Append(txt1)
                .Append("; ")
                .Append(txt2)
                .Append("; ")
                .Append(txt3)
                .Append("; ... ]")
                .ToString()

and [<Sealed>] MapDebugView<'Key, 'Value when 'Key: comparison>(v: Map<'Key, 'Value>) =

    [<DebuggerBrowsable(DebuggerBrowsableState.RootHidden)>]
    member x.Items =
        v |> Seq.truncate 10000 |> Seq.map KeyValuePairDebugFriendly |> Seq.toArray

and [<DebuggerDisplay("{keyValue.Value}", Name = "[{keyValue.Key}]", Type = "")>] KeyValuePairDebugFriendly<'Key, 'Value>
    (keyValue: KeyValuePair<'Key, 'Value>) =

    [<DebuggerBrowsable(DebuggerBrowsableState.RootHidden)>]
    member x.KeyValue = keyValue

and KeyCollection<'Key, 'Value when 'Key: comparison>(parent: Map<'Key, 'Value>) =
    interface ICollection<'Key> with
        member _.Add _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Clear() =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Remove _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Contains x =
            parent.ContainsKey x

        member _.CopyTo(arr, index) =
            if isNull arr then
                nullArg "arr"

            if index < 0 then
                invalidArg "index" "index must be positive"

            if index + parent.Count > arr.Length then
                invalidArg "index" "array is smaller than index plus the number of items to copy"

            let mutable i = index

            for item in parent do
                arr.[i] <- item.Key
                i <- i + 1

        member _.IsReadOnly = true

        member _.Count = parent.Count

    interface IEnumerable<'Key> with
        member _.GetEnumerator() =
            (seq {
                for item in parent do
                    item.Key
            })
                .GetEnumerator()

    interface IEnumerable with
        member _.GetEnumerator() =
            (seq {
                for item in parent do
                    item.Key
            })
                .GetEnumerator()
            :> IEnumerator

and ValueCollection<'Key, 'Value when 'Key: comparison>(parent: Map<'Key, 'Value>) =
    interface ICollection<'Value> with
        member _.Add _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Clear() =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Remove _ =
            raise (NotSupportedException(SR.GetString(SR.mapCannotBeMutated)))

        member _.Contains x =
            parent.ContainsValue x

        member _.CopyTo(arr, index) =
            if isNull arr then
                nullArg "arr"

            if index < 0 then
                invalidArg "index" "index must be positive"

            if index + parent.Count > arr.Length then
                invalidArg "index" "array is smaller than index plus the number of items to copy"

            let mutable i = index

            for item in parent do
                arr.[i] <- item.Value
                i <- i + 1

        member _.IsReadOnly = true

        member _.Count = parent.Count

    interface IEnumerable<'Value> with
        member _.GetEnumerator() =
            (seq {
                for item in parent do
                    item.Value
            })
                .GetEnumerator()

    interface IEnumerable with
        member _.GetEnumerator() =
            (seq {
                for item in parent do
                    item.Value
            })
                .GetEnumerator()
            :> IEnumerator

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
[<RequireQualifiedAccess>]
module Map =

    [<CompiledName("IsEmpty")>]
    let isEmpty (table: Map<_, _>) =
        table.IsEmpty

    [<CompiledName("Add")>]
    let add key value (table: Map<_, _>) =
        table.Add(key, value)

    [<CompiledName("Change")>]
    let change key f (table: Map<_, _>) =
        table.Change(key, f)

    [<CompiledName("Find")>]
    let find key (table: Map<_, _>) =
        table.[key]

    [<CompiledName("TryFind")>]
    let tryFind key (table: Map<_, _>) =
        table.TryFind key

    [<CompiledName("Remove")>]
    let remove key (table: Map<_, _>) =
        table.Remove key

    [<CompiledName("ContainsKey")>]
    let containsKey key (table: Map<_, _>) =
        table.ContainsKey key

    [<CompiledName("Iterate")>]
    let iter action (table: Map<_, _>) =
        table.Iterate action

    [<CompiledName("TryPick")>]
    let tryPick chooser (table: Map<_, _>) =
        table.TryPick chooser

    [<CompiledName("Pick")>]
    let pick chooser (table: Map<_, _>) =
        match tryPick chooser table with
        | None -> raise (KeyNotFoundException())
        | Some res -> res

    [<CompiledName("Exists")>]
    let exists predicate (table: Map<_, _>) =
        table.Exists predicate

    [<CompiledName("Filter")>]
    let filter predicate (table: Map<_, _>) =
        table.Filter predicate

    [<CompiledName("Partition")>]
    let partition predicate (table: Map<_, _>) =
        table.Partition predicate

    [<CompiledName("ForAll")>]
    let forall predicate (table: Map<_, _>) =
        table.ForAll predicate

    [<CompiledName("Map")>]
    let map mapping (table: Map<_, _>) =
        table.Map mapping

    [<CompiledName("Fold")>]
    let fold<'Key, 'T, 'State when 'Key: comparison> folder (state: 'State) (table: Map<'Key, 'T>) =
        let entries = table.SortedEntries

        if entries.Length = 0 then
            state
        else
            let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt folder
            let mutable acc = state

            for e in entries do
                acc <- f.Invoke(acc, e.Key, e.Value)

            acc

    [<CompiledName("FoldBack")>]
    let foldBack<'Key, 'T, 'State when 'Key: comparison> folder (table: Map<'Key, 'T>) (state: 'State) =
        let entries = table.SortedEntries

        if entries.Length = 0 then
            state
        else
            let f = OptimizedClosures.FSharpFunc<_, _, _, _>.Adapt folder
            let mutable acc = state

            for i = entries.Length - 1 downto 0 do
                let e = entries[i]
                acc <- f.Invoke(e.Key, e.Value, acc)

            acc

    [<CompiledName("ToSeq")>]
    let toSeq (table: Map<_, _>) =
        table |> Seq.map (fun kvp -> kvp.Key, kvp.Value)

    [<CompiledName("FindKey")>]
    let findKey predicate (table: Map<_, _>) =
        table
        |> Seq.pick (fun kvp ->
            let k = kvp.Key in

            if predicate k kvp.Value then
                Some k
            else
                None)

    [<CompiledName("TryFindKey")>]
    let tryFindKey predicate (table: Map<_, _>) =
        table
        |> Seq.tryPick (fun kvp ->
            let k = kvp.Key in

            if predicate k kvp.Value then
                Some k
            else
                None)

    [<CompiledName("OfList")>]
    let ofList (elements: ('Key * 'Value) list) =
        Map<_, _>.ofList elements

    [<CompiledName("OfSeq")>]
    let ofSeq elements =
        Map<_, _>.Create elements

    [<CompiledName("OfArray")>]
    let ofArray (elements: ('Key * 'Value) array) =
        Map<_, _>.Create elements

    [<CompiledName("ToList")>]
    let toList (table: Map<_, _>) =
        table.ToList()

    [<CompiledName("ToArray")>]
    let toArray (table: Map<_, _>) =
        table.ToArray()

    [<CompiledName("Empty")>]
    let empty<'Key, 'Value when 'Key: comparison> = Map<'Key, 'Value>.Empty

    [<CompiledName("Count")>]
    let count (table: Map<_, _>) =
        table.Count

    [<CompiledName("Keys")>]
    let keys (table: Map<_, _>) =
        table.Keys

    [<CompiledName("Values")>]
    let values (table: Map<_, _>) =
        table.Values

    [<CompiledName("MinKeyValue")>]
    let minKeyValue (table: Map<_, _>) =
        table.MinKeyValue

    [<CompiledName("MaxKeyValue")>]
    let maxKeyValue (table: Map<_, _>) =
        table.MaxKeyValue
