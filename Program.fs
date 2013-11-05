
// NOTE: If warnings appear, you may need to retarget this project to .NET 4.0. Show the Solution
// Pad, right-click on the project node, choose 'Options --> Build --> General' and change the target
// framework to .NET 4.0 or .NET 4.5.

module SimpleLeafImp.Main

open System
open Microsoft.FSharp.Reflection

// Example l3 definition
 
// Modules
type Module =
    | A
    | B
    | F
    | O
    | BStart
    | BEnd
    | Plus of float
    | Minus of float
    | P of float option*float option
    | Clear
    with
        member this.Undef () =
            match this with
                | P (Some(x),Some(y)) -> P (None,None)
                | _ -> this
                
        override this.ToString() = 
            match this with
                | A -> "A"
                | B -> "B"
                | F -> "F"
                | O -> "@"
                | BStart -> "["
                | BEnd -> "]"
                | Plus i -> sprintf "+(%f)" i
                | Minus i -> sprintf "-(%f)" i
                | P (None,None) -> "?P(x,y)"
                | P (Some x,Some y) -> sprintf "?P(x=%f,y=%f)" x y
                | Clear -> "%"
                
        member this.CompareTo other =
            let GetUnionCaseName (x:'a) = 
                match FSharpValue.GetUnionFields(x, typeof<'a>) with
                | case, _ -> case.Name
            (GetUnionCaseName this) = (GetUnionCaseName other)

// Production structure
type Production =
    {
        Id          : string
        Left        : Module option
        Pred        : Module
        Right       : Module option
        Succ        : (Module option -> Module -> Module option -> Module list)
        Condition   : (Module option -> Module -> Module option -> bool)
        Prob        : float option
    }

// Turtle declaration (define the state of the turtle)
type TurtleState = 
    {
        Position : (float*float)
        Rotation : float
    }

type Turtle =
    {
        Stack     : TurtleState list
        State     : TurtleState
        InitState : TurtleState
    }

// LSystem structure
type LSystem =
    {   
        Axiom       : Module list
        Ignore      : Module list
        Productions : Production list        
        Interpets   : (Turtle*Module -> Turtle*Module)
        Turtle      : Turtle
    }


let rec PrintModules (ls:Module list) =
    match ls with 
        | [] -> printf "\n"
        | x::xl -> printf "%s " (x.ToString ()); PrintModules xl
        
        
// ls -> lsystem; start -> starting module list
let DerivationStep (ls:LSystem) (s:Module list) =    
    let rec clearList (l:Module list) n =
        match l with 
            | [] -> []
            | x::xl -> 
                match x with 
                    | BEnd when n = 0 -> l
                    | BEnd -> (clearList xl (n-1))
                    | BStart -> (clearList xl (n+1))
                    | _ -> (clearList xl n) 
                                                                                      
    let rec undefStep (l:Module list) (acc:Module list) =
        match l with
            | [] -> acc
            | x::xl -> undefStep xl (acc@[x.Undef ()])
        
    let rec interpetationStep (ml:Module list) (acc:Module list) (t:Turtle) =
        match ml with
            | [] -> acc
            | x::xl -> 
                match x with
                    | Clear -> interpetationStep (clearList xl 0) acc t
                    | _ -> 
                        let (t',x') = ls.Interpets (t,x)
                        interpetationStep xl (acc@[x']) t'
                        
    let getProduction (m:Module) (lc:Module option) (rc:Module option) =
        let rec getProduction' (ps:Production list) =
            match ps with
                | [] -> None
                | p::ps' ->
                    if (m.CompareTo p.Pred) && 
                       (p.Right.IsNone || (lc.IsSome && lc.Value.CompareTo p.Left.Value)) && 
                       (p.Left.IsNone || (rc.IsSome && rc.Value.CompareTo p.Right.Value)) && 
                       (p.Condition lc m rc) then
                        Some (p)
                    else
                        getProduction' ps'
        getProduction' ls.Productions
    
    let rec productionStep (ml:Module list) (lc:Module option) (rc:Module option) (acc:Module list) =
        match ml with
            | [] -> acc
            | x::xl ->
                match getProduction x lc rc with
                    | None -> productionStep xl (Some x) (if xl.Length > 1 then Some xl.[1] else None) (acc@[x])
                    | Some p -> 
                        //printf " App %s: " p.Id; PrintModules ((p.Succ lc x rc)); printf " Acc: "; PrintModules acc
                        productionStep xl (Some x) (if xl.Length > 1 then Some xl.[1] else None) (acc@(p.Succ lc x rc))
    
    // Ciclo di riscrittura
    let psl = productionStep s None (if s.Length > 1 then Some s.[1] else None) []
    // Ciclo di interpetazione
    interpetationStep (undefStep psl []) [] ls.Turtle
    
    
let rec DerivationSteps ls s n =
    if n > 0 then DerivationSteps ls (DerivationStep ls s) (n-1)
    else s
    
    
// LSystem definition
let lsystem3 =
    {
        Axiom = [ A ]
        Ignore = [ Plus 0.0; Minus 0.0]
        Productions =
            [
                {
                    Id = "p1"
                    Left = None
                    Pred = A
                    Right = None
                    Succ = (fun l p s -> [ BStart; Plus(1.0); B; BEnd; BStart; Minus(1.0); B; BEnd; F; P(None,None); A ])
                    Condition = (fun l p s -> true)
                    Prob = None
                };
                {
                    Id = "p2"
                    Left = None
                    Pred = B
                    Right = None
                    Succ = (fun l p s -> [ F; P(None,None); O; B])
                    Condition = (fun l p s -> true)
                    Prob = None
                };
                {
                    Id = "p3"
                    Left = None
                    Pred = P (None, None)
                    Right = None
                    Prob = None
                    Condition = (fun l p s -> 
                                match (l,p,s) with
                                   | (_,P(Some(x),Some(y)),_) -> (((y * y) + (((x - 1.41421) * (x - 1.41421)))/4.0) > 0.5) 
                                   | _ -> false)
                    Succ = (fun l p s -> 
                                match (l,p,s) with
                                    | (_,P(Some(x),Some(y)),_) -> [ BStart; Plus(2.0*y); F; BEnd; BStart; Minus(2.0*y); F; BEnd; Clear ]
                                    | _ -> failwith "???")
                }
            ]
        Turtle = 
            { 
                Stack = []
                InitState = { Position=(0.0,0.0); Rotation=0.0 } 
                State = { Position=(0.0,0.0); Rotation=0.0 } 
            }
        Interpets = (fun (t:Turtle,m:Module) ->
                        let rad f = f * 0.015707963   
                        let size = 0.2 
                        match m with 
                            | P(None,None) -> (t, P(Some(fst t.State.Position), Some(snd t.State.Position)))
                            | BStart -> ({ t with Stack=(t.State::t.Stack) }, BStart)
                            | BEnd -> ({ t with Stack=(List.tail t.Stack); State=(List.head t.Stack) }, BEnd)
                            | Plus i -> ({ t with State={t.State with Rotation=t.State.Rotation + 60.0 * i}}, Plus i)
                            | Minus i -> ({ t with State={t.State with Rotation=t.State.Rotation - 60.0 * i}}, Minus i)
                            | F -> 
                                let nx = ((fst t.State.Position)+cos(rad (float t.State.Rotation))*size)
                                let ny = ((snd t.State.Position)+sin(rad (float t.State.Rotation))*size)
                                ({ t with State={t.State with Position=(nx,ny)}}, F)
                            | _ -> (t,m)
                    )                       
    }

[<EntryPoint>]
let main args = 
    PrintModules (DerivationSteps lsystem3 lsystem3.Axiom 25)
    0

