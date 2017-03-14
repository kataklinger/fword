open System
open System.IO

let isSameObject = LanguagePrimitives.PhysicalEquality

type CwDictionary(filePath : string) = 
    
    let words = 
        File.ReadAllLines(filePath)
        |> Seq.choose (fun w -> 
               if String.IsNullOrEmpty(w) then None
               else Some w)
        |> Seq.map (fun w -> w.ToUpper())
        |> Seq.groupBy (fun w -> w.Length)
        |> Seq.map (fun (l, w) -> 
               (l, 
                w
                |> Set.ofSeq
                |> Array.ofSeq))
        |> Map.ofSeq
    
    member m.GetWords(lenght : int) = 
        match words.TryFind lenght with
        | Some opts -> opts
        | _ -> Array.empty

type CwField = 
    { Letter : char
      HorRef : int
      VerRef : int
      Count : int
      Conflicted : bool }
    
    member x.Clear() = 
        { x with Letter = 
                     if x.Count = 1 then '_'
                     else x.Letter
                 Count = x.Count - 1 }
    
    member x.Set(letter : char) = 
        { x with Letter = letter
                 Count = x.Count + 1
                 Conflicted = false }
    
    member x.MarkConflicted = { x with Conflicted = true }

type CwDirection = 
    | Horizontal
    | Vertical

type CwPattern(grid : CwField [,], dictionary : string array, direction : CwDirection, no : int, xs : int, ys : int, length : int) = 
    
    let offset = 
        let hor off = (ys, xs + off)
        let ver off = (ys + off, xs)
        if direction = Horizontal then hor
        else ver
    
    let mutable options = dictionary
    let mutable stamp = 0
    
    member m.FilterOptions(word : string, other : CwPattern) = 
        let index, letter = 
            match direction with
            | Horizontal -> (other.X - xs, ys - other.Y)
            | Vertical -> (other.Y - ys, xs - other.X)
        options |> Array.choose (fun o -> 
                       if o.[index] = word.[letter] then Some o
                       else None)
    
    member m.PruneOptions() = 
        let mask = 
            [| for i in 0..length - 1 -> 
                   let y, x = offset i
                   if grid.[y, x].Conflicted then grid.[y, x].Letter
                   else '_' |]
        
        let filter (mask : char array) (words : string array) = 
            let compareByMask mask word = 
                match Seq.compareWith (fun w m -> 
                          if m = '_' then 0
                          else (int w) - (int m)) word mask with
                | 0 -> None
                | _ -> Some word
            words |> Array.choose (compareByMask mask)
        
        options <- options |> filter mask
    
    member m.RestoreOptions() = 
        let filter (mask : char array) (words : string array) = 
            if mask |> Array.forall ((=) '_') then dictionary
            else 
                let compareByMask mask word = 
                    match Seq.compareWith (fun w m -> 
                              if m = '_' then 0
                              else (int w) - (int m)) word mask with
                    | 0 -> Some word
                    | _ -> None
                words |> Array.choose (compareByMask mask)
        options <- dictionary |> filter m.Letters
    
    member m.UpdateOptions(opts : string array) = options <- opts
    
    member m.Fill(word : string, step : int) = 
        stamp <- step
        options <- options |> Array.choose (fun w -> 
                                  if w <> word then Some w
                                  else None)
        for i in 0..(length - 1) do
            let y, x = offset i
            grid.[y, x] <- grid.[y, x].Set word.[i]
    
    member m.Undo() = 
        stamp <- 0
        let rec loop acc i = 
            if i < 0 then acc
            else 
                let y, x = offset i
                let value = grid.[y, x].Clear()
                grid.[y, x] <- value
                loop (value :: acc) (i - 1)
        loop [] (length - 1) |> List.choose (function 
                                    | { Count = 0; VerRef = ref } when direction = Horizontal -> Some ref
                                    | { Count = 0; HorRef = ref } when direction = Vertical -> Some ref
                                    | _ -> None)
    
    member m.MarkConflicted() = 
        for i in 0..(length - 1) do
            let y, x = offset i
            grid.[y, x] <- grid.[y, x].MarkConflicted
    
    member m.Dependant = 
        let getRef = 
            if direction = Horizontal then (fun x -> x.VerRef)
            else (fun x -> x.HorRef)
        [ for i in 0..(length - 1) -> 
              let y, x = offset i
              let field = grid.[y, x]
              (field.Count, getRef field) ]
    
    member m.Letters = 
        [| for i in 0..(length - 1) -> 
               let y, x = offset i
               grid.[y, x].Letter |]
    
    member m.Conflicted = 
        seq { 
            for i in 0..(length - 1) -> 
                let y, x = offset i
                grid.[y, x].Conflicted
        }
        |> Seq.exists id
    
    member m.Word = new String(m.Letters)
    member m.No = no
    member m.X = xs
    member m.Y = ys
    member m.Length = length
    member m.Direction = direction
    member m.Options = options
    member m.Count = options.Length
    member m.Stamp = stamp

type Crossword(filePath : string, dictionary : CwDictionary) = 
    let minPatternLength = 2
    let maxWordPoolLength = 10
    let rng = new Random()
    
    let grid = 
        let lines = File.ReadAllLines(filePath)
        
        let width = 
            (lines
             |> Seq.map (fun l -> l.Length)
             |> Seq.max)
        
        let mutable hor = -1
        let mutable ver = -1
        let vers = Array.create width 0
        Array2D.init<CwField> lines.Length width (fun y x -> 
            if lines.[y].[x] = '#' then 
                { Letter = '#'
                  HorRef = -1
                  VerRef = -1
                  Count = -1
                  Conflicted = false }
            else 
                if x = 0 || lines.[y].[x - 1] = '#' then hor <- hor + 1
                if y = 0 || lines.[y - 1].[x] = '#' then 
                    ver <- ver + 1
                    vers.[x] <- ver
                { Letter = '_'
                  HorRef = hor
                  VerRef = vers.[x]
                  Count = 0
                  Conflicted = false })
    
    let getPatterns direction start = 
        seq { 
            for y in 0..(grid.GetLength 0) - 1 do
                for x in 0..(grid.GetLength 1) - 1 do
                    let v = grid.[y, x]
                    if v.Count = 0 then yield (y, x, v)
        }
        |> Seq.groupBy (fun (y, x, g) -> 
               if direction = Horizontal then g.HorRef
               else g.VerRef)
        |> Seq.map (fun (rx, gr) -> 
               (rx, Seq.length gr, 
                gr
                |> Seq.map (fun (y, _, _) -> y)
                |> Seq.min, 
                gr
                |> Seq.map (fun (_, x, _) -> x)
                |> Seq.min))
        |> Seq.sortBy (fun (rx, _, _, _) -> rx)
        |> Seq.mapi 
               (fun i (_, len, y, x) -> new CwPattern(grid, dictionary.GetWords(len), direction, (start + i), x, y, len))
        |> Array.ofSeq
    
    let hPatterns = getPatterns Horizontal 0
    let vPatterns = getPatterns Vertical hPatterns.Length
    let spliter = new String(Array.create (grid.GetLength(1) * 2) '-')
    
    let orthogonal (pattern : CwPattern) = 
        if pattern.Direction = Horizontal then vPatterns
        else hPatterns
    
    let selectPattern queue = 
        let rec loop (min : CwPattern) (proc : CwPattern list) (rest : CwPattern list) = 
            let nmin, nproc, nrest = 
                match rest with
                | h :: t when h.Count < min.Count -> (h, min :: proc, t)
                | h :: t -> (min, h :: proc, t)
                | [] -> (min, proc, [])
            if nrest.IsEmpty then (nmin, nproc)
            else loop nmin nproc nrest
        match queue with
        | [] -> (None, [])
        | first :: others -> 
            let min, rest = loop first [] others
            (Some min, rest)
    
    let selectWord (pattern : CwPattern) = 
        let rec loop index count (options : string seq) output selected = 
            let newCnt, newSel, newOut = 
                match (index, selected) with
                | (i, h :: t) when i = h -> (count + 1, t, (Seq.head options) :: output)
                | _ -> (count, selected, output)
            if selected.IsEmpty then output
            else loop (index + 1) newCnt (Seq.tail options) newOut newSel
        if pattern.Count = 0 then None
        else 
            let count = (min pattern.Count maxWordPoolLength) - 1
            let ort = orthogonal pattern
            
            let selected = 
                [ for i in 0..count -> rng.Next(pattern.Count) ]
                |> List.distinct
                |> List.sort
                |> loop 0 0 pattern.Options []
                |> Seq.map (fun w -> 
                       let filtered = 
                           pattern.Dependant
                           |> Seq.choose (function 
                                  | (0, c) -> Some c
                                  | _ -> None)
                           |> Seq.map (fun c -> ort.[c])
                           |> Seq.choose (fun c -> 
                                  if c.Length > minPatternLength then Some c
                                  else None)
                           |> Seq.map (fun c -> (c, c.FilterOptions(w, pattern)))
                           |> List.ofSeq
                       (w, filtered))
                |> Seq.maxBy 
                       (fun (_, c) -> 
                       Seq.foldBack (fun (_, o : string array) acc -> acc * log (1. + (float o.Length))) c 1.)
            Some selected
    
    let backjump (start : CwPattern) = 
        start.MarkConflicted()
        let rec loop current undo buffer = 
            let ort = orthogonal current
            let append (left : CwPattern list) (right : CwPattern list) = 
                left @ right |> List.distinctBy (fun x -> x.No)
            
            let next = 
                current.Dependant |> List.choose (fun (_, r) -> 
                                         let p = ort.[r]
                                         if p.Stamp > current.Stamp then Some p
                                         else None)
            match append buffer next with
            | [] -> undo
            | npat :: nbuf -> loop npat (append next undo) nbuf
        
        let dest = 
            let local = 
                let ort = orthogonal start
                start.Dependant
                |> Seq.map (fun (_, r) -> ort.[r])
                |> Seq.maxBy (fun p -> p.Stamp)
            if local.Stamp > 0 then local
            else 
                start.RestoreOptions()
                (hPatterns, vPatterns)
                ||> Seq.append
                |> Seq.choose (fun p -> 
                       if p.Conflicted && p.Length > minPatternLength then Some p
                       else None)
                |> Seq.maxBy (fun p -> p.Stamp)
        
        if dest.Stamp > 0 then 
            let undo = (dest :: (loop dest [] [])) |> List.sortByDescending (fun p -> p.Stamp)
            
            let restore = 
                undo
                |> List.collect (fun p -> 
                       if isSameObject p dest then p.PruneOptions()
                       let ort = orthogonal p
                       p.Undo() |> List.choose (fun u -> 
                                       if ort.[u].Length > minPatternLength then Some ort.[u]
                                       else None))
                |> List.distinctBy (fun p -> p.No)
            restore |> List.iter (fun u -> u.RestoreOptions())
            Some undo
        else None
    
    member x.Solve(refreshRate : int) = 
        let rec loop step queue = 
            if step % refreshRate = 0 then 
                printfn "%s" spliter
                printfn "%A" step
                printfn "%s" spliter
                x.Print()
            let stop, nqueue = 
                match queue |> selectPattern with
                | (Some current, rest) -> 
                    match selectWord current with
                    | Some(word, crossed) -> 
                        current.Fill(word, step)
                        crossed |> Seq.iter (fun (p, o) -> p.UpdateOptions o)
                        (false, rest)
                    | None -> 
                        match backjump current with
                        | Some undone -> (false, undone @ queue)
                        | None -> (true, queue)
                | (None, _) -> (true, queue)
            match (stop, nqueue.IsEmpty) with
            | (true, true) -> true
            | (true, false) -> false
            | _ -> loop (step + 1) nqueue
        Seq.append hPatterns vPatterns
        |> Seq.choose (fun p -> 
               if p.Length > minPatternLength then Some p
               else None)
        |> List.ofSeq
        |> loop 1
    
    member x.Check() = 
        Seq.append hPatterns vPatterns
        |> Seq.choose (fun p -> 
               if p.Length > minPatternLength then 
                   if dictionary.GetWords(p.Word.Length) |> Array.exists ((=) p.Word) then None
                   else Some p.Word
               else None)
        |> List.ofSeq
    
    member x.Print() = 
        grid |> Array2D.iteri (fun y x f -> 
                    printf "%c " f.Letter
                    if x = grid.GetLength(1) - 1 then printf "\n")
    
    member x.Grid = grid
    member x.HW = hPatterns
    member x.VW = vPatterns

[<EntryPoint>]
let main argv = 
    let dictionary = new CwDictionary(@"words.txt")
    printfn "Dictionaries processed"
    let rec loop() = 
        let crossword = new Crossword(@"puzzle.txt", dictionary)
        if crossword.Solve(100) then 
            let errors = crossword.Check()
            if errors.IsEmpty then printfn "SUCCESS!"
            else printfn "ERRORS: %A!" errors
        else printfn "FAILED!"
        crossword.Print()
        printfn "press enter for another"
        Console.ReadLine() |> ignore
        loop()
    loop()
    0 // return an integer exit code
