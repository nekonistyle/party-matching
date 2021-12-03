From mathcomp Require Import all_ssreflect.

Require Import Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)

Section Seq.
  Lemma filter_size T p (s:seq T) : size (filter p s) <= size s.
  Proof. by rewrite size_filter count_size. Qed.

  Lemma filter_sizeP T p (s:seq T) :
    reflect (size (filter p s) < size s) (has (predC p) s).
  Proof.
    apply : (iffP idP).
    - elim : s =>[|x s IH]//=. case : ifP =>//=_ _. exact : filter_size.
    - elim : s =>[|x s IH]//=. by case : ifP.
  Qed.

  Fixpoint dropuntil (X:eqType) x (s:seq X) :=
    match s with
    | [::] => [::]
    | h :: s' => if x == h then s else dropuntil x s'
    end.

  Definition behind (X:eqType) (s:seq X) f b := b \in dropuntil f s.

  Lemma behind_head (X:eqType) (s:seq X) h b :
    behind (h :: s) h b = (b \in h :: s).
  Proof. by rewrite /behind /= eq_refl. Qed.

  Lemma mem_behind (X:eqType) (s:seq X) f b :
    behind s f b -> b \in s.
  Proof.
    rewrite /behind. elim : s =>[|h s IH]//=. case : ifP =>//_ H.
      by rewrite in_cons (IH H) orbT.
  Qed.

  Lemma behindxx (X:eqType) (s:seq X) x : x \in s -> behind s x x.
  Proof.
    elim : s =>[|h s IH]//. rewrite in_cons /behind =>/orP[/eqP->|Hx]//=.
    - by rewrite eq_refl mem_head.
    - case : ifP =>[/eqP->|_]; [by rewrite mem_head|exact : IH].
  Qed.

  Lemma behind_sub2seq (X:eqType) (s:seq X) f b :
    subseq [:: f; b] s -> behind s f b.
  Proof.
    elim : s =>[|h s IH]//=. rewrite /behind /=.
    case : ifP =>_; [by rewrite sub1seq in_cons =>->; exact : orbT|exact : IH].
  Qed.

  Lemma behindP (X:eqType) (s:seq X) f b:
    reflect (subseq [:: f; b] s || (f == b) && (f \in s)) (behind s f b).
  Proof.
    apply /(iffP idP)=>[|/orP[/behind_sub2seq|/andP[/eqP->/behindxx]]]//.
    rewrite /behind. elim : s =>[|h s IH]//=. rewrite in_cons.
    case : ifP =>[/eqP->|_/IH]//.
    rewrite in_cons =>/orP[/eqP->|]; [by rewrite eq_refl orbT|].
      by rewrite sub1seq =>->.
  Qed.

  Definition onth (T:Type) (s:seq T) n :=
    nth None [seq Some x | x <- s] n.

  Lemma onth0 (T:Type) x (s:seq T) :
    onth (x :: s) 0 = Some x.
  Proof. done. Qed.

  Lemma onth_cons (T:Type) x (s:seq T) n :
    onth (x :: s) n.+1 = onth s n.
  Proof. done. Qed.

  Lemma onth_mem (T:eqType) x (s:seq T) n:
    onth s n = Some x -> x \in s.
  Proof.
    rewrite /onth. elim : s =>[|h s IH]/= in n *; [by rewrite nth_nil|].
    case : n =>[|n]/=; [by case=>->; rewrite mem_head|move/IH].
    rewrite in_cons =>->. exact : orbT.
  Qed.

  Lemma onth_lt (T:eqType) x (s:seq T) n:
    onth s n = Some x -> n < size s.
  Proof.
    rewrite /onth. elim : s =>[|h s IH]/= in n *; [by rewrite nth_nil|].
      by case : n =>[|n]//=/IH.
  Qed.

  Lemma onth_index (T:eqType) x (s:seq T) :
    x \in s -> onth s (index x s) = Some x.
  Proof.
    move => xs. by rewrite /onth (@nth_map _ x) ?index_mem // nth_index.
  Qed.

  Lemma onth_uniq (T:eqType) t (s:seq T) n :
    uniq s -> onth s n = Some t -> index t s = n.
  Proof.
    rewrite /onth => /uniqP uniq st. apply /(uniq t).
    - by rewrite unfold_in /= index_mem (onth_mem st).
    - by rewrite unfold_in /= (onth_lt st).
    - move : (st). rewrite (nth_map t) ?(onth_lt st) // =>[[->]].
      exact : nth_index (onth_mem st).
  Qed.

  Fixpoint mysorted T (R:rel T) (s:seq T) :=
    if s is x :: s' then all (fun y => R y x ==> R x y) s' && mysorted R s'
    else true.

  Lemma mysorted_cat T (R:rel T) s1 s2 :
    mysorted R s1 -> mysorted R s2 ->
    all (fun x => all (fun y => R y x ==> R x y) s2) s1 ->
    mysorted R (s1 ++ s2).
  Proof.
    elim : s1 =>[|x s1 IHs1]//=.
    rewrite all_cat => /andP [->] Hs1 Hs2 /andP [->]/=. exact : IHs1.
  Qed.

  Lemma subseq_mysorted (T:eqType) (R:rel T) s1 s2:
    subseq s1 s2 -> mysorted R s2 -> mysorted R s1.
  Proof.
    elim : s2 =>[|h2 s2 IH]//= in s1 *; [by move =>/eqP->|].
    case : s1 =>[|h1 s1]//=. case : ifP =>[/eqP->|_ s12 /andP[_/(IH _ s12)]]//.
    move => s12 /andP[/allP H2]/(IH _ s12)->. rewrite andbT.
      by apply /allP => z /(mem_subseq s12)/H2.
  Qed.

  Function qsort T (R:rel T) (s:seq T) {measure size s} :=
    if s is x :: s'
    then qsort R [seq y <- s' | R y x] ++ x :: qsort R [seq y <- s' | ~~ R y x]
    else [::].
  Proof.
    - move => T R _ x s _/=. apply /ltP. by rewrite ltnS size_filter count_size.
    - move => T R _ x s _/=. apply /ltP. by rewrite ltnS size_filter count_size.
  Defined.

  Lemma my_qsort_ind T (R:rel T) (P:seq T -> Prop) :
    P [::] ->
    (forall x s, P [seq y <- s | R y x] ->
                 P [seq y <- s | ~~ R y x] -> P (x :: s)) ->
    forall s, P s.
  Proof.
      move => Hnil Hcons s.
      have [n] := ubnP (size s). elim : n s =>[|n IHn][|xs s]//= Hsize.
        by apply : Hcons; exact : IHn (leq_ltn_trans (filter_size _ _) Hsize).
    Qed.

  Lemma all_qsort T (R:rel T) p s : all p (qsort R s) = all p s.
  Proof.
    elim /(@my_qsort_ind _ R) : s =>[|x s]//=.
    rewrite [qsort R (_ :: _)]qsort_equation all_cat /==>->->.
    case : (p x) =>/=; last exact : andbF. elim : s =>[|y s]//=.
    case : ifP =>_/=<-; case : (p y)=>//=. exact : andbF.
  Qed.

  Lemma qsort_sorted T (R:rel T) s : transitive R -> mysorted R (qsort R s).
  Proof.
    move => Htrans.
    elim /(@my_qsort_ind _ R) : s =>[|x s IHs1 IHs2]//.
    rewrite qsort_equation. apply : mysorted_cat =>//=.
    - rewrite IHs2 andbT all_qsort.
        by apply : (sub_all _ (filter_all _ _)) => y /negbTE ->.
    - rewrite all_qsort.
      apply : (sub_all _ (filter_all _ _)) => y Hyx.
      rewrite Hyx implybT all_qsort /=.
      apply : (sub_all _ (filter_all _ _)) => z.
      case Hzy : (R z y)=>//. by rewrite (Htrans _ _ _ Hzy Hyx).
  Qed.

  Lemma perm_qsort (T:eqType) (R:rel T) s: perm_eq (qsort R s) s.
  Proof.
    elim /(@my_qsort_ind _ R) : s =>[|x s IHs1 IHs2]//.
    rewrite qsort_equation perm_catC /= perm_cons perm_sym
    -(perm_filterC (R^~ x)) perm_catC perm_sym. exact : perm_cat.
  Qed.

  Lemma qsort0 T (s:seq T) : qsort (fun _ _ => false) s = s.
  Proof.
    elim /(@my_qsort_ind T (fun _ _ => false)) : s =>[|x s IH1 IH2]//.
      by rewrite qsort_equation IH1 IH2 filter_pred0 filter_predT.
  Qed.
End Seq.

Section PUndup.
  Variable (T S:eqType).
  Variable (X:eqType).

  Function pUndup (s:seq (T * S * X)) {measure size s} : seq (T * S * X) :=
    match s with
    | [::] => [::]
    | h :: s => h :: pUndup [seq x <- s | h.1.1 != x.1.1 & h.1.2 != x.1.2 ]
    end.
  Proof.
    move => s' h s _. apply /ltP. exact : filter_size.
  Defined.

  Lemma my_pUndup_ind (P:seq (T * S * X) -> Prop) :
    P [::] ->
    (forall h s, P [seq x <- s | h.1.1 != x.1.1 & h.1.2 != x.1.2 ] ->
                 P (h :: s)) ->
    forall s, P s.
  Proof.
    move => Hnil Hcons s.
    have [n] := ubnP (size s).
    elim : n s =>[|n IH][|h s]//=. rewrite ltnS => Hsize. apply /Hcons /IH.
    exact : leq_ltn_trans (filter_size _ _) Hsize.
  Qed.

  Lemma pUndup_subseq s : subseq (pUndup s) s.
  Proof.
    elim /my_pUndup_ind : s =>[|h s IH]//=. rewrite pUndup_equation eq_refl.
    exact : subseq_trans IH (filter_subseq _ _).
  Qed.

  Lemma pUndup_uniquel s x y:
    x \in pUndup s -> y \in pUndup s -> x.1.1 = y.1.1 -> x = y.
  Proof.
    elim /my_pUndup_ind : s =>[|h s IH]//. rewrite pUndup_equation !in_cons.
    case : (x =P h) (y =P h) =>[->|xh][->|yh]//=.
    - move =>_ /(mem_subseq (pUndup_subseq _)).
        by rewrite mem_filter =>/andP[/andP[/eqP]].
    - move =>/(mem_subseq (pUndup_subseq _)).
        by rewrite mem_filter eq_sym =>/andP[/andP[/eqP]].
  Qed.

  Lemma pUndup_uniquer s x y:
    x \in pUndup s -> y \in pUndup s -> x.1.2 = y.1.2 -> x = y.
  Proof.
    elim /my_pUndup_ind : s =>[|h s IH]//. rewrite pUndup_equation !in_cons.
    case : (x =P h) (y =P h) =>[->|xh][->|yh]//=.
    - move =>_/(mem_subseq (pUndup_subseq _)).
        by rewrite mem_filter =>/andP[/andP[_/eqP]].
    - move =>/(mem_subseq (pUndup_subseq _)).
        by rewrite mem_filter [h.1.2 == _]eq_sym =>/andP[/andP[_/eqP]].
  Qed.

  Lemma pUndup_maximal s x:
    x \in s -> has (fun m => (m.1.1 == x.1.1) || (m.1.2 == x.1.2)) (pUndup s).
  Proof.
    elim /my_pUndup_ind : s =>[|h s IH]//. rewrite pUndup_equation in_cons.
    case : (x =P h) =>[->|_ xs]/=; [by rewrite eq_refl|].
    rewrite -implyNb negb_or. apply /implyP =>H. apply : IH.
      by rewrite mem_filter H.
  Qed.

  Lemma pUndup_minimal s x:
    x \in s ->
          has (fun m => ((m.1.1 == x.1.1) || (m.1.2 == x.1.2)) && behind s m x)
              (pUndup s).
  Proof.
    elim /my_pUndup_ind : s =>[|h s IH]// Hx. rewrite pUndup_equation /=.
    rewrite -implyNb negb_and negb_or.
    apply /implyP =>/orP[]; [|by rewrite behind_head Hx].
    move : Hx. rewrite in_cons =>/orP[/eqP->|xs H]; [by rewrite eq_refl|].
    apply : (sub_has _ (IH _)) =>[z /andP[]|]; [|by rewrite mem_filter H].
    rewrite /behind /=.
    case : ifP H =>[/eqP->/andP[/negbTE->/negbTE->]|_ hx zx]//. rewrite zx /=.
    elim : s {xs IH}=>[|h' s IH]//=.
    case : ifP =>_/=.
    - case : ifP =>[/eqP<-|]//. apply /mem_subseq =>/=.
        by rewrite eq_refl filter_subseq.
    - case : ifP =>[/eqP<-/mem_behind|]//. apply /mem_subseq.
      exact : subseq_trans (filter_subseq _ _) (subseq_cons _ _).
  Qed.

End PUndup.

Section Pairs.
  Variable (T S:finType).

  Fixpoint pairs_def (fs:S -> seq T) (t:T) (ss:seq S) (nt:nat) :
    seq (T * S * (nat * nat)) :=
    match ss with
    | [::] => [::]
    | s :: ss => let st := fs s in
                 let ns := index t st in
                 if ns < size st
                 then (t,s,(nt,ns)) :: pairs_def fs t ss nt.+1
                 else pairs_def fs t ss nt.+1
    end.

  Lemma pairs_def_index (fs:S -> seq T) (ss:seq S) t s n:
    (t \in fs s) && (s \in ss) -> 
    (t,s,(index s ss + n,index t (fs s))) \in pairs_def fs t ss n.
  Proof.
    move =>/andP[Ht Hs].
      elim : ss =>[|h ss IH]//= in Hs n *. move : Hs. rewrite in_cons eq_sym.
      case : ifP =>[/eqP->|_/IH/(_ n.+1)]/=.
      * by rewrite index_mem Ht add0n mem_head.
      * rewrite addnS addSn. case : ifP =>[_|_->]//. rewrite in_cons =>->.
        exact : orbT.
  Qed.

  Lemma ex_pairs_defP (fs:S -> seq T) (xt:T) (ss:seq S) t s n:
    reflect (exists nt ns, (t,s,(nt,ns)) \in pairs_def fs xt ss n)
            [&& t == xt, (t \in fs s) & (s \in ss)].
  Proof.
    apply (iffP and3P)=>[[/eqP<- Ht Hs]|[nt][ns]].
    - exists (index s ss + n), (index t (fs s)).
      apply : pairs_def_index. by rewrite Ht Hs.
    - elim : ss =>[|h ss IH]//= in n *. rewrite index_mem in_cons.
      case : ifP =>[|_/IH[->->->]]; [|by rewrite orbT].
        by rewrite !in_cons => Hh /orP[/eqP[->->_ _]|/IH[->->->]];
                                 [rewrite !eq_refl Hh|rewrite orbT].
  Qed.

  Lemma mem_pairs_def (fs:S -> seq T) (xt:T) (ss:seq S) t s nt ns n:
    (t,s,(nt,ns)) \in pairs_def fs xt ss n -> 
                      [/\ t == xt, (t \in fs s) & (s \in ss)].
  Proof.
    move => H. apply /and3P /ex_pairs_defP. exists nt; exists ns. exact : H.
  Qed.

  Lemma pairs_defP (fs:S -> seq T) (xt:T) (ss:seq S) t s nt ns n:
    (forall s, uniq (fs s)) -> uniq ss ->
    reflect [&& t == xt, n <= nt, onth (fs s) ns == Some t &
                                  onth ss (nt - n) == Some s]
            ((t,s,(nt,ns)) \in pairs_def fs xt ss n).
  Proof.
    move => uniqt uniqs.
    apply /(iffP idP).
    - elim : ss {uniqs} =>[|h ss IH]//= in n *. case : ifP =>[|_/IH].
      + rewrite index_mem in_cons => Ht /orP[/eqP[->-><-->]|/IH].
        * by rewrite subnn onth0 onth_index // !eq_refl /= !andbT.
        * case : nt {IH}=>[|nt]; [by case /and4P|move =>/and3P[/eqP->[Hlt]]].
            by rewrite eq_refl subSS subSn // ltnW.
      + case : nt {IH}=>[|nt]; [by case /and3P|move =>/and3P[/eqP->Hlt]].
          by rewrite eq_refl subSS subSn //= ltnW.
    - elim : ss uniqs =>[_|h ss IH /andP[Hh uniqs]]/= in nt n *;
                    [by rewrite /onth /= nth_nil =>/and4P[]|].
      case : ifP =>[|Hlt /and4P[txt]].
      + rewrite index_mem in_cons => ht /and4P[txt].
        case : ltngtP =>[Hlt _ Ht Hs||->_/eqP/(onth_uniq (uniqt _))<-]//.
        * apply /orP. right. apply /IH=>//. move : Ht Hs =>->.
          case : nt =>[|nt]// in Hlt *. by rewrite txt /onth Hlt subSS subSn.
        * move /eqP : txt =>->. rewrite /onth subnn /==>/eqP[<-].
            by rewrite eq_refl.
      + case : ltngtP =>[||->_ /eqP/onth_mem Ht /eqP Hs]//.
        * case : nt =>[|nt]// Hn _ Ht. rewrite subSn // onth_cons => Hs.
          apply /IH =>//. apply /and4P. by split.
        * move /eqP : txt Hs Ht Hlt =>->.
            by rewrite subnn onth0 index_mem =>[[->]]->.
  Qed.

  Definition pairs (ft:T -> seq S) (fs:S -> seq T) :
    seq (T * S * (nat * nat)) :=
    flatten (codom (fun t => pairs_def fs t (ft t) 0)).

  Lemma pairs_index (ft:T -> seq S) (fs:S -> seq T) (t:T) (s:S):
    (t \in fs s) && (s \in ft t) ->
    (t,s,(index s (ft t),index t (fs s))) \in pairs ft fs.
  Proof.
    move /pairs_def_index. move /(_ 0). rewrite addn0 => H. apply /flattenP.
    exists (pairs_def fs t (ft t) 0) =>//. apply /codomP. by exists t.
  Qed.

  Lemma ex_pairsP (ft:T -> seq S) (fs:S -> seq T) (t:T) (s:S):
    reflect (exists nt ns, (t,s,(nt,ns)) \in pairs ft fs)
            ((t \in fs s) && (s \in ft t)).
  Proof.
    apply /(iffP idP)
    =>[H|[nt][ns]/flattenP[x/codomP[xt->]/mem_pairs_def[/eqP<-->->]]]//.
    have /ex_pairs_defP : [&& t == t, t \in fs s & s \in ft t]
      by rewrite eq_refl.
    case /(_ 0) =>[nt][ns] Hts. exists nt, ns.
    apply /flattenP. exists (pairs_def fs t (ft t) 0) =>//.
    apply /codomP. by exists t.
  Qed.

  Lemma mem_pairs (ft:T -> seq S) (fs:S -> seq T) (t:T) (s:S) nt ns:
    (t,s,(nt,ns)) \in pairs ft fs -> (t \in fs s) && (s \in ft t).
  Proof.
    move => H. apply /ex_pairsP. by exists nt, ns.
  Qed.

  Lemma pairsP (ft:T -> seq S) (fs:S -> seq T) (t:T) (s:S) nt ns:
    (forall t, uniq (fs t)) -> (forall s, uniq (ft s)) ->
    reflect ((onth (fs s) ns == Some t) && (onth (ft t) nt == Some s))
            ((t,s,(nt,ns)) \in pairs ft fs).
  Proof.
    move => uniqs uniqt.
    apply /(iffP flattenP)
    =>[[ss /codomP[xt->]/(pairs_defP _ _ _ _ _ _ uniqs (uniqt _))
           /and4P[/eqP-> _->]]|/andP[Ht Hs]]; [by rewrite subn0|].
    exists (pairs_def fs t (ft t) 0).
    - apply /codomP. by exists t.
    - apply /pairs_defP =>//. by rewrite eq_refl subn0 Ht Hs.
  Qed.
End Pairs.

Section MkCouple.
  Variable (R:rel (nat * nat)).
  Variable (T S:finType).

  Definition mkCouple (ft:T -> seq S) (fs:S -> seq T) :
    seq (T * S * (nat * nat)) :=
    pUndup (qsort (fun x y => R x.2 y.2) (pairs ft fs)).

  Lemma mkCouple_kindness (ft:T -> seq S) (fs:S -> seq T) t s nt ns :
    (t,s,(nt,ns)) \in mkCouple ft fs -> (t \in fs s) && (s \in ft t).
  Proof.
    move /(mem_subseq (pUndup_subseq _)).
    by rewrite (perm_mem (perm_qsort _ _))=>/mem_pairs.
  Qed.

  Lemma mkCouple_uniquel (ft:T -> seq S) (fs:S -> seq T) t s s' nt nt' ns ns':
    (t,s,(nt,ns)) \in mkCouple ft fs ->
                      (t,s',(nt',ns')) \in mkCouple ft fs ->
                                           [/\ s = s', nt = nt' & ns = ns'].
  Proof.
    move => H H'. by case : (pUndup_uniquel H H' (erefl _)).
  Qed.

  Lemma mkCouple_uniquer (ft:T -> seq S) (fs:S -> seq T) t t' s nt nt' ns ns':
    (t,s,(nt,ns)) \in mkCouple ft fs ->
                      (t',s,(nt',ns')) \in mkCouple ft fs ->
                                           [/\ t = t', nt = nt' & ns = ns'].
  Proof.
    move => H H'. by case : (pUndup_uniquer H H' (erefl _)).
  Qed.

  Lemma mkCouple_maximal (ft:T -> seq S) (fs:S -> seq T) t s:
    (t \in fs s) && (s \in ft t) ->
    has (fun m => (m.1.1 == t) || (m.1.2 == s)) (mkCouple ft fs).
  Proof.
    case /ex_pairsP =>[nt][ns].
    rewrite -(perm_mem (perm_qsort (fun x y => R x.2 y.2) _)).
    exact : pUndup_maximal.
  Qed.

  Hypothesis (Htrans: transitive R).

  Lemma mkCouple_minimal (ft:T -> seq S) (fs:S -> seq T) t s:
    (t \in fs s) && (s \in ft t) ->
    has (fun m => ((m.1.1 == t) || (m.1.2 == s)) &&
                  let x := (index s (ft t), index t (fs s)) in
                  (R x m.2 ==> R m.2 x))
        (mkCouple ft fs).
  Proof.
    move => /pairs_index ts. move : (ts).
    rewrite -(perm_mem (perm_qsort (fun x y => R x.2 y.2) _))
               =>/pUndup_minimal.
    apply : sub_has => m /=/andP[->]/behindP/orP[|/andP[/eqP->_]];
                         [|exact /implyP].
    have sndtrans : transitive (fun x y: (T * S * (nat * nat)) => R x.2 y.2)
      := fun _ _ _ xy yz => Htrans xy yz.
    move =>/subseq_mysorted. move =>/(_ _ (qsort_sorted _ sndtrans))/=.
      by rewrite !andbT.
  Qed.

End MkCouple.
