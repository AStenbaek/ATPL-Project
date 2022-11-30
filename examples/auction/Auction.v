From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import TranslationUtils.
From ConCert.Examples.Auction Require Import AuctionData.

From ConCert.Execution Require Import Blockchain.

From Coq Require Import String.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.
Import BaseTypes.
Open Scope list.

Import Prelude.Maps.

Module AuctionContract.

  Import AcornBlockchain.
  Module Init.
    Import AuctionData.Notations.
    Definition auction_init : expr :=
      [| \c : SCtx => \dl : Nat => \params : InitParameter =>
           {eConstr State mkState} {eConstr AuctionState NotSoldYet} ({eConstr Maybe Nothing} {eTy (tyInd Nat)}) (init_item params) (init_end params)
      |].

    Compute (indexify nil auction_init).

    MetaCoq Unquote Definition init :=
      (expr_to_tc Σ' (indexify nil auction_init)).
  End Init.

  Module Receive.
    (* Context {Base : ChainBase}. *)

    Import AuctionData.Notations.
    Notation "'case' x : ci 'return' ty2 'of' | p1 -> b1 | p2 -> b2 | p3 -> b3 | p4 -> b4" :=
      (eCase (ci_to_types ci) ty2 x [(p1,b1); (p2,b2); (p3,b3); (p4,b4)])
        (in custom expr at level 2,
            p1 custom pat at level 4,
            p2 custom pat at level 4,
            p3 custom pat at level 4,
            p4 custom pat at level 4,
            b1 custom expr at level 4,
            b2 custom expr at level 4,
            b3 custom expr at level 4,
            b4 custom expr at level 4,
            ci custom case_info at level 4,
            ty2 custom type at level 4).


   Notation "'#Just' a" := [| {eConstr (to_string_name <% option %>) "Some"} {eTy [! Result!]} {a}|]
                           (in custom expr at level 0,
                               a custom expr at level 1).

   Notation "'#Pair' a b" := [| {eConstr Prod "pair"}
                               {eTy (tyInd State)}
                               {eTy actions_ty} {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).

   Notation "'#Nothing'" := (eApp (eConstr (to_string_name <% option %>) "None") (eTy [!Result!]))
                             (in custom expr at level 0).

   Notation "'Transfer' a b" :=
    [| {eConstr SActionBody "Act_transfer"} {b} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

   Global Program Instance CB : ChainBase :=
     build_chain_base nat Nat.eqb _ _ _ _ Nat.odd. (* Odd addresses are addresses of contracts :) *)
   Next Obligation.
     eapply NPeano.Nat.eqb_spec.
   Defined.
   Next Obligation.
     Admitted.

(*    Import Serializable. *)
(*    Section Serialize. *)
(*   Hint Rewrite to_list_of_list of_list_to_list : hints. *)
(*   Global Program Instance addr_map_serialize : Serializable addr_map_coq := *)
(*     {| serialize m := serialize (to_list m); *)
(*        deserialize l := option_map of_list (deserialize l); |}. *)
(*   Next Obligation. *)
(*     intros. cbn. rewrite deserialize_serialize. cbn. *)
(*     now autorewrite with hints. *)
(*   Defined. *)

(*   Global Instance State_serializable : Serializable State_coq := *)
(*     Derive Serializable State_coq_rect<mkState_coq>. *)

(*   Global Instance Msg_serializable : Serializable Msg_coq := *)
(*     Derive Serializable Msg_coq_rect<Donate_coq, GetFunds_coq, Claim_coq>. *)

(* End Serialize. *)

   Compute (@address_is_contract CB).

   Definition auction : expr :=
     [|
       \"chain" : SChain => \"c" : SCtx => \"m" : Msg => \"s" : State =>
         let "now" : Nat := cur_time "chain" in
         let "sender" : Address := {eConst (to_string_name <% Ctx_from %>)} "c" in
         let "owner" : Address := {eConst (to_string_name <% Ctx_origin %>)} "c" in
         let "amount" : Money := {eConst (to_string_name <% Ctx_amount %>)} "c" in
         let "balance" : Money := {eConst (to_string_name <% Ctx_contract_balance %>)} "c" in
         let "previous_bid" : Money := "balance" - "amount" in
         case "m" : Msg return Maybe Result of
           | Bid ->
             if (case auction_state "s" : AuctionState return Bool of
                      | NotSoldYet -> True
                      | Sold "address" -> False) &&
                ("now" <=n ({eConst (to_string_name <% end_coq %>)} "s")) &&
                ({eConst (to_string_name <% (@address_is_contract CB) %>)} "sender") && (* HACK: *)
                ("previous_bid" < "amount")
             then
               let "new_state" : State := {eConstr State mkState} {eConstr AuctionState NotSoldYet} ({eConstr Maybe Just} {eTy (tyInd Nat)} "sender")
                                  (item "s") (end "s") in
               case highest_bidder "s" : Maybe Address return Maybe Result of
                   | Nothing -> #Just #Pair "new_state" (Nil SActionBody)
                   | Just "previous_bidder" -> #Just #Pair "new_state" (Cons SActionBody (Transfer "previous_bid" "previous_bidder") (Nil SActionBody))
             else #Nothing : Maybe Result
           | View -> #Just (#Pair "s" (Nil SActionBody))
           | ViewHighestBid -> #Just (#Pair "s" (Nil SActionBody))
           | Finalize -> #Nothing (* TODO: *)
    |].

    Compute (indexify nil auction).

    MetaCoq Unquote Definition receive :=
      (expr_to_tc Σ' (indexify nil auction)).

  End Receive.

End AuctionContract.
