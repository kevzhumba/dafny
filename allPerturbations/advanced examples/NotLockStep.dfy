// RUN: /compile:0 /nologo /noNLarith /noCheating:1 /rlimit:1000000


include "../armada/code/dafny/util/option.s.dfy"
include "../armada/code/dafny/util/collections/seqs.s.dfy"
include "../armada/code/dafny/util/collections/seqs.i.dfy"
include "../armada/code/dafny/fl/spec/refinement.s.dfy"
include "../armada/code/dafny/fl/util/invariants.i.dfy"

/*
var x := 0;
x := x + 1;
x := x + 1;
output x;
------------------------
var x := 0;
x := x + 2;
output x;
 */

module Prelude {
    type Tid = int

    datatype Event = Event(value: int)
}

module Layer0 {
    import opened Prelude
    import opened util_option_s
    import opened GeneralRefinementModule
    import opened InvariantsModule
    
    datatype State = State(x: int, log: seq<Event>)

    datatype MainPC = MainPC0 | MainPC1 | MainPC2

    datatype TotalState = TotalState(shared: State, local: Option<MainPC>)

    predicate SharedInit(s: State)
    {
        && s.x == 0
        && s.log == []
    }

    predicate Init(s: TotalState)
    {
        && SharedInit(s.shared)
        && s.local == Some(MainPC0)
    }

    predicate Inv(s: TotalState)
    {
        match s.local
            case None => true
            case Some(pc) => 
                match pc {
                    case MainPC0 => s.shared.x == 0
                    case MainPC1 => s.shared.x == 1
                    case MainPC2 => s.shared.x == 2
                }
    }

    function GetInv(): iset<TotalState>
    {
        iset s | Inv(s)
    }

    predicate Inc(s: State, s': State)
    {
        && s'.x == s.x + 1
        && s'.log == s.log
    }

    predicate Print(s: State, s': State, v: int)
    {
        && s'.x == s.x
        && s'.log == s.log + [Event(v)]
    }


    predicate Next(s: TotalState, s': TotalState)
    {
        match s.local
            case Some(pc) => 
                match pc {
                    case MainPC0 => 
                        && Inc(s.shared, s'.shared)
                        && s'.local == Some(MainPC1)
                    case MainPC1 => 
                        && Inc(s.shared, s'.shared)
                        && s'.local == Some(MainPC2)
                    case MainPC2 => 
                        && Print(s.shared, s'.shared, s.shared.x)
                        && s'.local.None?
                }
            case None => false
    }

    function GetSpec(): Spec<TotalState>
    {
        Spec(iset s | Init(s), iset s, s' | Next(s, s') :: StatePair(s, s'))
    }

    lemma lemma_InvIsInvariant()
        ensures IsSpecInvariant(GetInv(), GetSpec())
    {
        lemma_EstablishSpecInvariantPure(GetInv(), GetSpec());
    }
}

module Layer1 {
    import opened Prelude
    import opened util_option_s
    import opened GeneralRefinementModule
 

    datatype State = State(x: int, log: seq<Event>)

    datatype MainPC = MainPC0 | MainPC1

    datatype TotalState = TotalState(shared: State, local: Option<MainPC>)

    predicate SharedInit(s: State)
    {
        && s.x == 0
        && s.log == []
    }

    predicate Init(s: TotalState) 
    {
        && SharedInit(s.shared)
        && s.local == Some(MainPC0)
    }

    predicate IncBy2(s: State, s': State)
    {
        && s'.x == s.x + 2
        && s'.log == s.log
    }

    predicate Print(s: State, s': State, v: int)
    {
        && s'.x == s.x
        && s'.log == s.log + [Event(v)]
    }

    predicate Next(s: TotalState, s': TotalState)
    {
        || s' == s
        || match s.local
            case Some(pc) => 
                match pc {
                    case MainPC0 => 
                        && IncBy2(s.shared, s'.shared)
                        && s'.local == Some(MainPC1)
                    case MainPC1 => 
                        && Print(s.shared, s'.shared, s.shared.x)
                        && s'.local.None?
                }
            case None => false
    }

    function GetSpec(): Spec<TotalState>
    {
        Spec(iset s | Init(s), iset s, s' | Next(s, s') :: StatePair(s, s'))
    }
}

module Sim01 {
    import opened util_option_s
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i
    import opened GeneralRefinementModule
    import opened InvariantsModule
    import Low = Layer0
    import High = Layer1

    predicate RefinementPredicate(l: Low.TotalState, h: High.TotalState) 
    {
        l.shared.log == h.shared.log
    }

    function RefinementSet(): iset<RefinementPair<Low.TotalState, High.TotalState>>
    {
        iset l, h | RefinementPredicate(l, h) :: RefinementPair(l, h)
    }

    predicate SimulationRelation(l: Low.TotalState, h: High.TotalState) 
    {
        && l.shared.log == h.shared.log
        && (l.local.None? <==> h.local.None?)
        && match l.local
           case None => true
           case Some(lpc) => 
            match lpc 
            case MainPC0 => 
                && h.local.v == High.MainPC0
                && h.shared.x == 0
            case MainPC1 => 
                && h.local.v == High.MainPC0
                && h.shared.x == 0
            case MainPC2 => 
                && h.local.v == High.MainPC1
                && h.shared.x == 2
    }

    function GetSimulationSet(): iset<RefinementPair<Low.TotalState, High.TotalState>>
    {
        iset l, h | SimulationRelation(l, h) :: RefinementPair(l, h)
    }

    lemma lemma_Refinement()
        ensures SpecRefinesSpec(Low.GetSpec(), High.GetSpec(), RefinementSet())
    {
        var l_spec := Low.GetSpec();
        var h_spec := High.GetSpec();
        var relation := RefinementSet();
        forall lb | BehaviorSatisfiesSpec(lb, l_spec)
            ensures BehaviorRefinesSpec(lb, h_spec, relation)
        {
            assert lb[0] in l_spec.init;
            var h0 := High.TotalState(High.State(0, []), Some(High.MainPC0));
            assert RefinementPair(lb[0], h0) in relation;
            assert h0 in h_spec.init;

            var hb := [h0];
            var li := 0;

            while li < |lb| - 1
                invariant 0 <= li < |lb|
                invariant |hb| == li + 1
                invariant BehaviorSatisfiesSpec(hb, h_spec)
                invariant forall i :: 0 <= i <= li ==> SimulationRelation(lb[i], hb[i])
            {
                var l := lb[li];
                var l' := lb[li + 1];
                var h := last(hb);
                Low.lemma_InvIsInvariant();
                lemma_SpecInvariantHoldsAtStep(lb, li, l_spec, Low.GetInv());
                assert BehaviorSatisfiesSpec(lb, l_spec);
                assert l in Low.GetInv() && Low.Inv(l);
                assert SimulationRelation(l, h);
                assert StatePair(l, l') in l_spec.next;
                var h': High.TotalState;
                if l.local.Some? {
                    match l.local.v
                        case MainPC0 => {
                            assert l'.shared.log == l.shared.log;
                            assert l'.local.Some?;
                            h' := h;
                            assert SimulationRelation(l', h');
                            assert StatePair(h, h') in h_spec.next;
                        }
                        case MainPC1 => {
                            h' := High.TotalState(High.State(l'.shared.x, l'.shared.log), Some(High.MainPC1));
                            assert SimulationRelation(l', h');
                            assert StatePair(h, h') in h_spec.next;
                        }
                        case MainPC2 => {
                            h' := High.TotalState(High.State(l'.shared.x, l'.shared.log), None);
                            assert SimulationRelation(l', h');
                            assert StatePair(h, h') in h_spec.next;
                        }
                }
                hb := hb + [h'];
                li := li + 1;
            }
            assert lb == lb[..li+1];
            var lh_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| :: RefinementRange(i, i));
            forall i, j |
                0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
                ensures RefinementPair(lb[i], hb[j]) in relation
            {}
            assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
        }
    }
}
