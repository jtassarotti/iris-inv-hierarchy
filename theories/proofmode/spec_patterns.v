From stdpp Require Export strings.
From iris.proofmode Require Import tokens.
Set Default Proof Using "Type".

Inductive goal_kind := GSpatial | GModal | GPersistent.

Record spec_goal := SpecGoal {
  spec_goal_kind : goal_kind;
  spec_goal_negate : bool;
  spec_goal_frame : list string;
  spec_goal_hyps : list string;
  spec_goal_done : bool
}.

Inductive spec_pat :=
  | SForall : spec_pat
  | SName : string → spec_pat
  | SPureGoal : bool → spec_pat
  | SGoal : spec_goal → spec_pat
  | SAutoFrame : goal_kind → spec_pat.

Definition goal_kind_modal (k : goal_kind) : bool :=
  match k with GModal => true | _ => false end.
Definition spec_pat_modal (p : spec_pat) : bool :=
  match p with
  | SGoal g => goal_kind_modal (spec_goal_kind g)
  | SAutoFrame k => goal_kind_modal k
  | _ => false
  end.

Module spec_pat.
Inductive state :=
  | StTop : state
  | StAssert : spec_goal → state.

Fixpoint parse_go (ts : list token) (k : list spec_pat) : option (list spec_pat) :=
  match ts with
  | [] => Some (reverse k)
  | TName s :: ts => parse_go ts (SName s :: k)
  | TBracketL :: TAlways :: TFrame :: TBracketR :: ts =>
     parse_go ts (SAutoFrame GPersistent :: k)
  | TBracketL :: TFrame :: TBracketR :: ts =>
     parse_go ts (SAutoFrame GSpatial :: k)
  | TModal :: TBracketL :: TFrame :: TBracketR :: ts =>
     parse_go ts (SAutoFrame GModal :: k)
  | TBracketL :: TPure :: TBracketR :: ts => parse_go ts (SPureGoal false :: k)
  | TBracketL :: TPure :: TDone :: TBracketR :: ts => parse_go ts (SPureGoal true :: k)
  | TBracketL :: TAlways :: ts => parse_goal ts GPersistent false [] [] k
  | TBracketL :: ts => parse_goal ts GSpatial false [] [] k
  | TModal :: TBracketL :: ts => parse_goal ts GModal false [] [] k
  | TModal :: ts => parse_go ts (SGoal (SpecGoal GModal true [] [] false) :: k)
  | TForall :: ts => parse_go ts (SForall :: k)
  | _ => None
  end
with parse_goal (ts : list token)
    (ki : goal_kind) (neg : bool) (frame hyps : list string)
    (k : list spec_pat) : option (list spec_pat) :=
  match ts with
  | TMinus :: ts =>
     guard (¬neg ∧ frame = [] ∧ hyps = []);
     parse_goal ts ki true frame hyps k
  | TName s :: ts => parse_goal ts ki neg frame (s :: hyps) k
  | TFrame :: TName s :: ts => parse_goal ts ki neg (s :: frame) hyps k
  | TDone :: TBracketR :: ts =>
     parse_go ts (SGoal (SpecGoal ki neg (reverse frame) (reverse hyps) true) :: k)
  | TBracketR :: ts =>
     parse_go ts (SGoal (SpecGoal ki neg (reverse frame) (reverse hyps) false) :: k)
  | _ => None
  end.
Definition parse (s : string) : option (list spec_pat) :=
  parse_go (tokenize s) [].

Ltac parse s :=
  lazymatch type of s with
  | list spec_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some ?pats => pats | _ => fail "invalid list spec_pat" s
              end
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | spec_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some [?pat] => pat | _ => fail "invalid spec_pat" s
              end
  end.
End spec_pat.
