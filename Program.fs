// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.
open System.IO
open System.IO.MemoryMappedFiles
open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop
let read (start:int64) (n:int64) (m:MemoryMappedFile) = m.CreateViewStream(start,n)
let bytes(m:Stream) = let b = new MemoryStream() in m.CopyTo b; b.ToArray()
let say = printfn "%s"
let side f a = f a;a
let comment s a = printfn "%s" s
let promptf pfs = Printf.kprintf(fun s -> printf "%s: " s; System.Console.ReadLine()) pfs
let exitf i pfs = Printf.kprintf(fun s -> printf "Exit: %s" s; exit i) pfs
let do_help() = ()
let _b_uint64 b = System.BitConverter.ToUInt64(b,0)
let _b_uint32 b = System.BitConverter.ToUInt32(b,0)
let _b_uint16 b = System.BitConverter.ToUInt16(b,0)
let _uint64_b (i:uint64) = System.BitConverter.GetBytes i
let _uint32_b (i:uint32) = System.BitConverter.GetBytes i
let _uint16_b (i:uint16) = System.BitConverter.GetBytes i
let _int64_b (i:int64) = System.BitConverter.GetBytes(i)
let _b_int64 b = System.BitConverter.ToInt64(b,0)
let _int32_b (i:int32) = System.BitConverter.GetBytes(i)
let _b_int32 b = System.BitConverter.ToInt32(b,0)
let word_size = sizeof<nativeint>
let _b_native (i:nativeint) = 
    match word_size with
    |4 -> i.ToInt32()|> _int32_b
    |8 -> i.ToInt64()|> _int64_b
    |_ -> failwith "Bad word size: %i" word_size
let _native_b (b:byte[]) = 
    match word_size with
    |4 -> b |> _b_int32 |> nativeint
    |8 -> b |> _b_int64 |> nativeint
    |_ -> failwith "Bad word size: %i" word_size
let arg (f:'a->'b->'c) (v:'a) = f v
let MAGIC_NUMBER = 0x00424950u // = "PIB\0"
type BigArray(ptr:nativeint,size:int64) as x =
    let s = new UnmanagedMemoryStream(ptr,size)
    let get_slice(a,b) = 
        let a = match a with |None -> 0L     |Some(i) -> i
        let b = match b with |None -> size-1L|Some(i) -> i
        a,b
    member x.Pointer = ptr
    member x.Length = size
    member x.Item with get(v:int64) = Marshal.ReadByte(ptr+nativeint v) and set(v:int64)(b:byte) = Marshal.WriteByte(nativeint v+ptr, b)
    member x.GetSlice (a:int64 option,b:int64 option) = let a,b = get_slice(a,b) in let n = ptr |> int64 in BigArray(n+a|>nativeint,n+a+b)
    //let a,b = get_slice(a,b) in s.Seek(a,SeekOrigin.Begin)|>ignore;s.AsyncRead (b-a|>int) |> Async.RunSynchronously 
    member x.SetSlice (a,b,v':BigArray) = 
        let a,b = get_slice(a,b) 
        let count = b-a
        let stop  = ptr+nativeint count
        let p = v'.Pointer
        let rec inner i j = 
            if i<>stop then
                Marshal.WriteIntPtr(i,Marshal.ReadIntPtr(j))
                inner (i+1n)(j+1n)
        inner (ptr+nativeint a) v'.Pointer
    member x.Stream = s
    interface System.Collections.Generic.IEnumerable<byte> with
        member x.GetEnumerator() = 
            let mutable v = -1L
            {new System.Collections.IEnumerator with
                member y.Current = x.Item(v)|>box
                member y.MoveNext() = System.Threading.Interlocked.Increment(&v)|>ignore; v = x.Length
                member y.Reset() = v <- -1L
            }
        member x.GetEnumerator() = 
            let mutable v = -1L
            {new System.Collections.Generic.IEnumerator<byte> with
                member y.Current = x.Item(v)
                member y.MoveNext() = System.Threading.Interlocked.Increment(&v)|>ignore; v = x.Length
                member y.Reset() = v <- -1L
            }
    new(size) = let ptr = Marshal.AllocHGlobal(nativeint size) in BigArray(ptr,size)
    static member ToByteArray (x:BigArray) = 
        let b = Array.zeroCreate(int x.Length)
        x.Stream.Read(b,0,b.Length)|>ignore
        b
    static member OfStream(m:Stream) = 
        let x = new BigArray(m.Length)
        m.CopyTo x.Stream
        x
    static member OfByteArray(b:byte[]) = BigArray(Marshal.UnsafeAddrOfPinnedArrayElement(b,0),b.LongLength)
    static member IndexOfStarting (j:byte) (x:BigArray) (i:int64) : int64 = 
        if i = x.Length then raise(System.Collections.Generic.KeyNotFoundException())
        if x.[i] = j then i else BigArray.IndexOfStarting j x i
    static member IndexOf j x  :int64= BigArray.IndexOfStarting j x 0L
type BigType<'T> = {map:'T->BigArray;unmap:BigArray->'T;elementsize:int}
type BigArray<'T>(bigarray:BigArray,bt:BigType<'T>) = 
    let e = int64 bt.elementsize
    let e' = e-1L
    let n = bigarray.Length/e
    let get_slice(a,b) = 
        let a = match a with |None -> 0L|Some(i) -> i
        let b = match b with |None -> n |Some(i) -> i
        a,b
    member x.InnerBigArray = bigarray
    member x.Length = n
    member x.Item 
        with get(i) : 'T = let pos = e * i in bigarray.[pos..pos+e'] |> bt.unmap
        and set i j = let pos = e * i in bigarray.[pos..pos+e'] <- bt.map j
    member x.SetSlice(a,b,v':BigArray) = 
        let a,b = get_slice(a,b)
        bigarray.SetSlice(Some(e*a),Some((e*b)-1L),v')
    member x.GetSlice(a,b) = 
        let a,b = get_slice(a,b)
        bigarray.GetSlice(Some(e*a),Some((e*b)-1L))
    member x.InnnerBigType = bt
    interface System.Collections.Generic.IEnumerable<'T> with
        member x.GetEnumerator() = 
            let mutable v = -1L
            {new System.Collections.IEnumerator with
                member y.Current = x.Item(v)|>box
                member y.MoveNext() = System.Threading.Interlocked.Increment(&v)|>ignore; v = x.Length
                member y.Reset() = v<-0L
            }
        member x.GetEnumerator() = 
            let mutable v = -1L
            {new System.Collections.Generic.IEnumerator<'T> with
                member y.Current = x.Item(v)
                member y.Current = x.Item(v)|>box
                member y.MoveNext() = System.Threading.Interlocked.Increment(&v)|>ignore; v = x.Length
                member y.Reset() = v<-0L
                member x.Dispose() = ()
            }
    static member OfArray (arr:'T[]) (bt:BigType<'T>) = 
        let n = arr.Length*bt.elementsize

    static member OfStream map unmap elementsize (m:Stream) = new BigArray<_>(BigArray.OfStream(m),{map=map;unmap=unmap;elementsize=elementsize})
    static member Concat (v:BigArray<BigArray<'T>>) =
        if v.Length = 0L then raise(System.ArgumentOutOfRangeException("Need to have at least one element in the array")) else
        let bt = v.[0L].InnnerBigType
        let total : int64 = 
            let rec inner i j = 
                if j = v.Length then i else
                inner (i+v.[j].Length) (j+1L)
            inner 0L 0L
        let dest = BigArray<'T>(BigArray(total),bt)
        let rec inner i j =
            if i = v.Length then dest else
            let b = v.[i].InnerBigArray
            let n = j+b.Length
            dest.[j..n-1L]<-b
            inner (i+1L) j
        inner 0L 0L
    static member Concat (v:BigArray<BigArray>) =
        let total : int64 = 
            let rec inner i j = 
                if j = v.Length then i else
                inner (i+v.[j].Length) (j+1L)
            inner 0L 0L
        let dest = BigArray(total)
        let rec inner i j =
            if i = v.Length then dest else
            let b = v.[i]
            let n = j+b.Length
            dest.[j..n-1L]<-b
            inner (i+1L) j
        inner 0L 0L
    static member Map f (x:BigArray<'a>) (bt:BigType<'b>) = 
        let dest = BigArray(x.Length*int64 bt.elementsize)
        let rec inner i = if i = x.Length then dest else dest.[i..i+int64 bt.elementsize-1L] <- x.[i]|>f i|>bt.map; inner (i+int64 bt.elementsize)
        BigArray<'b>(inner 0L,bt)
    static member MapInPlace f (x:BigArray<'a>) =
        let rec inner i = 
            if i <> x.Length then
                x.[i] <- x.[i]|>f i
                inner (i+1L)
        inner 0L
type BigRefArray<'T>(bigarray:BigArray) = 
    let v = BigArray<nativeint>(bigarray,{map=_b_native>>BigArray.OfByteArray;unmap=BigArray.ToByteArray>>_native_b;elementsize=word_size})
    member x.Item 
        with get i   = v.[i] |> NativePtr.ofNativeInt |> NativePtr.get
        and  set i j = v.[i] <- NativePtr.toNativeInt <| &&j
    member x.GetSlice(a,b)   = BigArray<nativeint>.Map(fun i a -> a |> NativePtr.ofNativeInt |> NativePtr.get) (v.GetSlice(a,b)) v.InnnerBigType
    member x.SetSlice(a,b,c) = BigArray<nativeint>.MapInPlace(fun i a -> a |> NativePtr.ofNativeInt |> NativePtr.get) (v.GetSlice(a,b))
type PibIndex= 
    {Length:int64;Positions:BigArray<int64>}
    static member HeaderSize = 12L
    static member OfBigArray (s:BigArray) = 
        let magic_number = s.[..3L] |> BigArray.ToByteArray |> _b_uint32
        if magic_number <> MAGIC_NUMBER then exitf -1 "Bad magic number: %i" magic_number
        let length = s.[4L..11L] |> BigArray.ToByteArray |> _b_uint64 |> int64
        let pos = BigArray<int64>(s.[12L..12L+((length-1L)*8L)],{map = _int64_b>>BigArray.OfByteArray;unmap=(fun i -> i|>BigArray.ToByteArray|>_b_int64);elementsize=8})
        {Length=length;Positions=pos}
    static member OfStream (s:MemoryMappedFile) = 
        let magic_number = s |> read 0L 4L |> bytes |> _b_uint32
        if magic_number <> MAGIC_NUMBER then exitf -1 "Bad magic number: %i" magic_number
        let length = s |> read 4L 8L |> bytes |> _b_uint64 |> int64
        let pos = s.CreateViewStream(12L,length)
        //BigArray<int64>(s.[12L..12L+((length-1L)*8L)],_int64_b>>BigArray.OfByteArray,(fun i -> i.ToArray()|>_b_int64),8)
        //{Length=length;Positions=BigArray(0L)}
        ()
type PibNode = 
    {MD5:byte[];Name:string;Type:string;Length:int64;Data:BigArray}
    static member BigType = 
        {
            map = fun (x:PibNode) ->
                    [|
                        BigArray.OfByteArray x.MD5
                        BigArray.OfByteArray (System.Text.Encoding.UTF8.GetBytes x.Type)
                        BigArray.OfByteArray [|0uy|]
                        BigArray.OfByteArray (System.Text.Encoding.UTF8.GetBytes x.Name)
                        BigArray.OfByteArray [|0uy|]
                        x.Data
                    |]
                    |> BigArray.Concat
            unmap = fun b ->
                let md5 = b.[..15L]|>BigArray.ToByteArray
                let n = BigArray.IndexOfStarting 0uy b 16L
                let t = BigArray.IndexOfStarting 0uy b (n+1L)
                let l = b.[t+1L..t+8L]|>BigArray.ToByteArray|>_b_int64
                let d = b.[t+9L..l+t+9L]
                {MD5=md5;Name=b.[16L..n-1L]|>BigArray.ToByteArray|>System.Text.Encoding.UTF8.GetString;Type=b.[n+1L..t-1L]|>BigArray.ToByteArray|>System.Text.Encoding.UTF8.GetString;Length=l;Data=d}
        }
type Pib(PibNodes:PibNode[]) = 
    member x.Run() = ()
    static member OfBigArray b = 
        let index = PibIndex.OfBigArray(b)
        let nodes = BigArray.Map (fun _ i -> b.[i..]|>PibNode.OfBigArray) index.Positions
        nodes
[<EntryPoint>]
let main argv = 
    let argv' = argv|>Array.map (fun s -> s.ToLower())
    match argv' with
    |[||]
    |[|"help"|] -> 
        do_help()
        0
    |[|"run"|]
    |[|"execute"|] ->
        let file = argv.[argv.Length-1]
        using (File.Open(file,FileMode.Open)) BigArray.OfStream
        |> Pib.OfBigArray
        0