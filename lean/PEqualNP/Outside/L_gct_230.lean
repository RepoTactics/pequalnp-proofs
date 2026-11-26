import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_gct_230
open Module
open Submodule (span)
open LinearMap (ker)
open Equiv (swap)
open Pi (single)
open Matrix (mulVec)
open Submodule (equivMapOfInjective)
open Matrix (permanent)
alias A0:=mul_eq_zero
alias A1:=Pi.add_apply
alias A4:=Pi.smul_apply
alias A5:=smul_eq_mul
alias A6:=Submodule.mem_inf
alias A7:=one_ne_zero
alias A8:=ite_false
alias A9:=ite_true
alias B4:=false_or
alias B5:=or_false
alias B6:=Submodule.mem_map
alias B7:=OfNat.ofNat_ne_zero
alias B8:=add_zero
alias C0:=zero_add
alias C1:=Pi.single_apply
alias C2:=Fin.sum_univ_four
alias C3:=mul_zero
alias C4:=Submodule.mem_map_of_mem
alias C5:=Submodule.mem_sup
alias C6:=Submodule.mem_span_singleton
alias C7:=LinearMap.mem_ker
alias C8:=eq_self_iff_true
alias C9:=if_neg
alias D1:=add_assoc
alias D2:=left_ne_zero_of_mul
alias D4:=neg_eq_zero
alias D5:=ne_of_lt
alias D6:=Submodule.smul_mem
alias D7:=ne_eq
alias D8:=Bool.and_eq_true
alias D9:=or_self
alias E4:=true_or
alias E5:=or_true
alias E6:=pow_eq_zero_iff
alias E7:=Submodule.finrank_mono
alias E8:=Finset.sum_add_distrib
alias E9:=map_add
alias F4:=zero_mul
alias F5:=Or.imp_right
alias F6:=finrank_bot
alias F7:=mul_add
alias F8:=Submodule.sub_mem
alias F9:=right_ne_zero_of_mul
alias G0:=two_ne_zero
alias G1:=one_smul
alias G2:=zero_smul
alias G3:=Pi.sub_apply
alias G4:=sub_self
alias G5:=inv_mul_cancel₀
alias G8:=one_mul
alias G9:=zero_ne_one
alias H0:=smul_smul
alias H3:=Submodule.finrank_sup_add_finrank_inf_eq
alias H4:=Submodule.finrank_le
alias H5:=map_zero
alias H8:=Submodule.map_comp
alias H9:=false_and
alias I0:=and_false
alias I1:=true_and
alias I3:=and_true
alias I4:=map_smul
alias I9:=eq_bot_iff
alias K2:=LinearEquiv.finrank_eq
alias K3:=Finset.sum_congr
alias K8:=le_sup_left
alias L0:=div_ne_zero
alias L1:=List.map_cons
alias L4:=bne_iff_ne
alias L5:=Submodule.mem_bot
alias L6:=LinearEquiv.finrank_map_eq
alias L7:=List.getD_cons_zero
alias L8:=not_false_eq_true
alias L9:=Equiv.swap_apply_left
alias M0:=Submodule.ne_bot_iff
alias M1:=Submodule.eq_top_of_finrank_eq
alias M2:=Submodule.span_le
alias M3:=Submodule.eq_of_le_of_finrank_eq
alias M7:=Module.finrank_fin_fun
alias N0:=div_mul_cancel₀
alias N2:=Int.cast_zero
alias N3:=List.sum_cons
alias N4:=pow_ne_zero
alias N5:=decide_eq_true_eq
alias N6:=Submodule.mem_sup_right
alias N7:=Pi.zero_apply
alias N8:=Set.not_subset
alias N9:=Fintype.sum_prod_type
alias O0:=Equiv.swap_apply_def
alias O3:=finrank_span_singleton
alias O4:=Submodule.map_span
alias O6:=Set.image_singleton
alias P0:=Submodule.mem_span_singleton_self
alias P5:=Submodule.map_mono
alias P6:=Set.singleton_subset_iff
alias P7:=Submodule.mem_sup_left
alias P8:=List.getD_cons_succ
alias P9:=Submodule.subset_span
alias Q0:=mul_eq_zero_of_right
alias Q2:=Submodule.finrank_lt
lemma M9 {n:ℕ} (g:Equiv.Perm (Fin (n+1))->ℂ):
  ∑ σ,g σ= ∑ a:Fin (n+1),∑ τ:Equiv.Perm (Fin n),
   g (Equiv.Perm.decomposeFin.symm (a,τ)):=by
 rw[<- Equiv.Perm.decomposeFin.symm.sum_comp,N9]
abbrev Fq:=Fin 4
lemma afC (M:Matrix Fq Fq ℂ):permanent M=
  (M 0 0*M 1 1+ M 0 1*M 1 0)*(M 2 2*M 3 3+ M 2 3*M 3 2)+(M 0 0*M 1 2+ M 0 2*M 1 0)*(M 2 1*M 3 3+ M 2 3*M 3 1)+(M 0 0*M 1 3+ M 0 3*M 1 0)*(M 2 1*M 3 2+ M 2 2*M 3 1)+(M 0 1*M 1 2+ M 0 2*M 1 1)*(M 2 0*M 3 3+ M 2 3*M 3 0)+(M 0 1*M 1 3+ M 0 3*M 1 1)*(M 2 0*M 3 2+ M 2 2*M 3 0)+(M 0 2*M 1 3+ M 0 3*M 1 2)*(M 2 0*M 3 1+ M 2 1*M 3 0):=by
 simp only[permanent];rw[M9];simp only[M9 (n:=2),M9 (n:=1),M9 (n:=0)];simp only[Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.prod_univ_succ,Fin.prod_univ_zero,
  Equiv.Perm.decomposeFin_symm_apply_zero,Equiv.Perm.decomposeFin_symm_apply_succ,
  Fintype.sum_unique]
 simp +decide [O0];ring
abbrev Mt:=Fq× Fq->ℂ
abbrev Sq:=Submodule ℂ Mt
def Bm:Mt:=λq=> if q.1=q.2 then 2 else 1
def p4 (M:Mt):ℂ:=
  (M (0,0)*M (1,1)+ M (0,1)*M (1,0))*(M (2,2)*M (3,3)+ M (2,3)*M (3,2))+(M (0,0)*M (1,2)+ M (0,2)*M (1,0))*(M (2,1)*M (3,3)+ M (2,3)*M (3,1))+(M (0,0)*M (1,3)+ M (0,3)*M (1,0))*(M (2,1)*M (3,2)+ M (2,2)*M (3,1))+(M (0,1)*M (1,2)+ M (0,2)*M (1,1))*(M (2,0)*M (3,3)+ M (2,3)*M (3,0))+(M (0,1)*M (1,3)+ M (0,3)*M (1,1))*(M (2,0)*M (3,2)+ M (2,2)*M (3,0))+(M (0,2)*M (1,3)+ M (0,3)*M (1,2))*(M (2,0)*M (3,1)+ M (2,1)*M (3,0))
lemma ago (t:Mt):
  permanent (Matrix.of λ(i j:Fq)=>(if i=j then (2:ℂ) else 1)+ t (i,j))=p4 (Bm+ t):=by
 rw[afC];simp[p4,Bm,Matrix.of_apply]
lemma agn (c:ℂ) (M:Mt):p4 (c•M)=c^4*p4 M:=by
 simp only[p4,A4,A5];ring
lemma acZ (t:Mt):p4 t=5*p4 ((1:ℂ)•Bm+ t)-10*p4 ((2:ℂ)•Bm+ t)
  +10*p4 ((3:ℂ)•Bm+ t)-5*p4 ((4:ℂ)•Bm+ t)+ p4 ((5:ℂ)•Bm+ t):=by
 simp only[p4,A1,A4,A5,Bm];simp;ring
lemma Ud (L:Sq) (f:∀ t∈L,p4 (Bm+ t)=65) (t:Mt) (h:t∈L) (c:ℂ):
  p4 (c•Bm+ t)=65*c^4:=by
 have a:∀ d:ℂ,d≠0->p4 (d•Bm+ t)=65*d^4:=by
  intro d g
  have e:d•Bm+ t=d•(Bm+ d⁻¹•t):=by
   rw[smul_add,H0,mul_inv_cancel₀ g,G1]
  rw[e,agn,f _ (L.smul_mem _ h)];ring
 by_cases b:c=0
 .subst b
  rw[G2,C0,acZ,a 1 (by norm_num),a 2 (by norm_num),a 3 (by norm_num),
   a 4 (by norm_num),a 5 (by norm_num)]
  norm_num
 .exact a c b
lemma Pe (L:Sq) (a:∀ t∈L,p4 (Bm+ t)=65):Bm∉ L:=by
 intro h;have :=a (-Bm) (L.neg_mem h);rw[add_neg_cancel]at this;simp[p4]at this
def fk (L:Sq) (d:∀ t∈L,p4 (Bm+ t)=65) (X:Mt)
  (e:X∈L ⊔ span ℂ {Bm}) (b:p4 X=0):X∈L:=by
 obtain⟨t,a,m,g,rfl⟩:=C5.1 e;obtain⟨c,rfl⟩:=C6.1 g;rw[add_comm,Ud L d t a c]at b
 have f:c=0:=by
  have :c^4=0:=by grind
  exact E6 (by norm_num) |>.1 this
 subst f;simpa using a
lemma du {V: Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (L:Submodule ℂ V) (x:V) (e:x∉ L):
  finrank ℂ ↥(L ⊔ span ℂ {x})=finrank ℂ L+1:=by
 have a:L ⊓ span ℂ {x}= ⊥ :=by
  rw[I9];intro v hv;obtain⟨hvL,d⟩:=A6.1 hv;obtain⟨c,rfl⟩:=C6.1 d;by_cases b:c=0
  .simp[b]
  .exact absurd ((L.smul_mem_iff b).1 hvL) e
 have f:x≠0:=by
  intro h;apply e;rw[h];exact L.zero_mem
 have :=H3 L (span ℂ {x});rw[a,F6,B8,O3 f]at this;exact this
lemma dx {V W: Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] (K:Submodule ℂ V) (p:V→ₗ[ℂ] W):
  finrank ℂ (K.map p)+ finrank ℂ ↥(K ⊓ ker p)=finrank ℂ K:=by
 have h:=LinearMap.finrank_range_add_finrank_ker (p.domRestrict K);rw[LinearMap.range_domRestrict]at h
 have a:(ker (p.domRestrict K)).map K.subtype=K ⊓ ker p:=by
  rw[LinearMap.ker_domRestrict,Submodule.map_comap_subtype]
 have b:finrank ℂ ((ker (p.domRestrict K)).map K.subtype)=
   finrank ℂ (ker (p.domRestrict K)):=
  (K2 (equivMapOfInjective _ K.injective_subtype _)).symm
 rw[a]at b;omega
def Zx (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65) (e:finrank ℂ L=6)
  {m:ℕ} (p:Mt→ₗ[ℂ] (Fin m->ℂ)) (h:∀ X,p X=0->p4 X=0):
  7≤ m+ finrank ℂ ↥(L ⊓ ker p):=by
 set C:=L ⊔ span ℂ {Bm} with f
 have i:finrank ℂ C=7:=by rw[f,du L Bm (Pe L b),e]
 have j:=dx C p
 have k:finrank ℂ (C.map p)≤ m:=by
  have :=H4 (C.map p);simpa using this
 have d:C ⊓ ker p≤ L ⊓ ker p:=by
  intro X g;obtain⟨c,a⟩:=A6.1 g;exact A6.2 ⟨fk L b X c (h X a),a⟩
 have l:=E7 d;omega
def ac0 (X:Mt) (h:∀ c d:Fq,c≠d->X (0,c)*X (1,d)+ X (0,d)*X (1,c)=0):
  p4 X=0:=by
 simp only[p4];grind
def ac1 (X:Mt) (h:∀ c d:Fq,c≠d->X (0,c)*X (2,d)+ X (0,d)*X (2,c)=0):
  p4 X=0:=by
 simp only[p4];grind
def ac2 (X:Mt) (h:∀ c d:Fq,c≠d->X (0,c)*X (3,d)+ X (0,d)*X (3,c)=0):
  p4 X=0:=by
 simp only[p4];grind
def ac3 (X:Mt) (h:∀ c d:Fq,c≠d->X (1,c)*X (2,d)+ X (1,d)*X (2,c)=0):
  p4 X=0:=by
 simp only[p4];grind
def ac4 (X:Mt) (h:∀ c d:Fq,c≠d->X (1,c)*X (3,d)+ X (1,d)*X (3,c)=0):
  p4 X=0:=by
 simp only[p4];grind
def ac5 (X:Mt) (h:∀ c d:Fq,c≠d->X (2,c)*X (3,d)+ X (2,d)*X (3,c)=0):
  p4 X=0:=by
 simp only[p4];grind
def Pd (r s:Fq) (b:r≠s) (X:Mt)
  (h:∀ c d:Fq,c≠d->X (r,c)*X (s,d)+ X (r,d)*X (s,c)=0):p4 X=0:=by
 have a:∀ c d:Fq,c≠d->X (s,c)*X (r,d)+ X (s,d)*X (r,c)=0:=by
  intro c d e;have :=h d c (Ne.symm e);grind
 fin_cases r<;>fin_cases s
 .exact absurd rfl b
 .exact ac0 X h
 .exact ac1 X h
 .exact ac2 X h
 .exact ac0 X a
 .exact absurd rfl b
 .exact ac3 X h
 .exact ac4 X h
 .exact ac1 X a
 .exact ac3 X a
 .exact absurd rfl b
 .exact ac5 X h
 .exact ac2 X a
 .exact ac4 X a
 .exact ac5 X a
 .exact absurd rfl b
def af (r:Fq):Mt→ₗ[ℂ] (Fq->ℂ) where
 toFun X:=λj=> X (r,j)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma bu (r:Fq) (X:Mt) (j:Fq):af r X j=X (r,j):=rfl
def Pb (r:Fq) (X:Mt) (h:∀ j,X (r,j)=0):p4 X=0:=by
 have a:∀ r:Fq,r≠r+1:=by decide
 have b:r≠r+1:=a r;apply Pd r (r+1) b X;intro c d _;rw[h c,h d];ring
lemma WJ (L:Sq) (d:∀ t∈L,p4 (Bm+ t)=65) (r:Fq) (t:Mt) (e:t∈L)
  (b:∀ j,t (r,j)=Bm (r,j)):False:=by
 have a:=d (-t) (L.neg_mem e)
 have c:p4 (Bm+ -t)=0:=Pb r _ (λj=> by simp[b j])
 rw[c]at a;norm_num at a
lemma LZ (L:Sq) (d:∀ t∈L,p4 (Bm+ t)=65) (r:Fq):
  L.map (af r)≠ ⊤ :=by
 intro b
 have c:(λj=> Bm (r,j))∈L.map (af r):=by rw[b];trivial
 obtain⟨t,e,a⟩:=B6.1 c
 exact WJ L d r t e (λj=> by rw[<- bu r t j,a])
lemma dk {K:Sq} (h:0< finrank ℂ K):∃ X∈K,X≠0:=by
 have b:K≠ ⊥ :=by
  intro a;rw[a,F6]at h;exact lt_irrefl 0 h
 exact (M0 K).1 b
lemma M5 (P:Submodule ℂ (Fq->ℂ)) (h:∀ j:Fq,(single j (1:ℂ):Fq->ℂ)∈P):
  P= ⊤ :=by
 rw[eq_top_iff];intro v _
 have hv:v= ∑ j:Fq,v j•(single j (1:ℂ):Fq->ℂ):=by
  ext i;simp[Finset.sum_apply,C1]
 rw[hv]
 exact Submodule.sum_mem _ (λj _=> P.smul_mem _ (h j))
lemma Ir (P:Submodule ℂ (Fq->ℂ)) (v:Fq->ℂ) (x:ℂ) (a:x≠0)
  (h:x•v∈P):v∈P:=(P.smul_mem_iff a).1 h
def ag6:∀ c j:Fq,j=c\/j=c+1\/j=c+2\/j=c+3:=by decide
def ajr:∀ a b:Fq,a≠b-> ∃ e f:Fq,∀ j:Fq,j=a\/j=b\/j=e\/j=f:=by
 decide
def VX (r s c:Fq):Mt→ₗ[ℂ] (Fin 6->ℂ) where
 toFun X:= ![X (r,c+1),X (r,c+2),X (r,c+3),X (s,c+1),X (s,c+2),X (s,c+3)]
 map_add' X Y:=by ext i;fin_cases i<;>simp
 map_smul' a X:=by ext i;fin_cases i<;>simp
def YN (r s a b e f:Fq):Mt→ₗ[ℂ] (Fin 6->ℂ) where
 toFun X:= ![X (r,a)- X (r,b),X (s,a)+ X (s,b),X (r,e),X (r,f),X (s,e),X (s,f)]
 map_add' X Y:=by ext i;fin_cases i<;>simp<;>ring
 map_smul' a X:=by ext i;fin_cases i<;>simp<;>ring
lemma Zv (L:Sq) (G:∀ t∈L,p4 (Bm+ t)=65) (V:finrank ℂ L=6)
  (r s:Fq) (S:r≠s):∃ X∈L,X≠0/\(∀ j,X (r,j)=0)/\(∀ j,X (s,j)=0):=by
 by_contra hK
 have H:∀ X∈L,(∀ j,X (r,j)=0)->(∀ j,X (s,j)=0)->X=0:=by
  intro X hX p g;by_contra O;exact hK ⟨X,hX,O,p,g⟩
 set k:=L.map (af r) with am;set l:=L.map (af s) with ao;have step1:∀ c:Fq,(single c (1:ℂ):Fq->ℂ)∈k\/
   (single c (1:ℂ):Fq->ℂ)∈l:=by
  intro c
  have R:∀ X,VX r s c X=0->(∀ j,j≠c->X (r,j)=0/\X (s,j)=0):=by
   intro X hX j hj;have A:=congrFun hX 0;have p:=congrFun hX 1;have g:=congrFun hX 2;have i:=congrFun hX 3;have B:=congrFun hX 4;have C:=congrFun hX 5;simp[VX]at A p g i B C;rcases ag6 c j with h | h | h | h
   .exact absurd h hj
   .subst h;exact⟨A,i⟩
   .subst h;exact⟨p,B⟩
   .subst h;exact⟨g,C⟩
  have hp:∀ X,VX r s c X=0->p4 X=0:=by
   intro X hX;apply Pd r s S X;intro u z F;by_cases hc:u=c
   .subst hc;have :=R X hX z (Ne.symm F);rw[this.1,this.2];ring
   .have :=R X hX u hc;rw[this.1,this.2];ring
  have hm:=Zx L G V (VX r s c) hp
  obtain⟨X,W,O⟩:=dk (K:=L ⊓ ker (VX r s c)) (by omega)
  obtain⟨P,Z⟩:=A6.1 W;have q:=R X (C7.1 Z);by_cases v:X (r,c)=0
  .by_cases w:X (s,c)=0
   .exfalso;apply O;apply H X P
    .intro j;by_cases hj:j=c
     .subst hj;exact v
     .exact (q j hj).1
    .intro j;by_cases hj:j=c
     .subst hj;exact w
     .exact (q j hj).2
   .right;apply Ir l _ (X (s,c)) w
    have :X (s,c)•(single c (1:ℂ):Fq->ℂ)=af s X:=by
     ext j;by_cases hj:j=c
     .subst hj;simp[bu]
     .simp[bu,hj,(q j hj).2]
    rw[this];exact C4 P
  .left;apply Ir k _ (X (r,c)) v
   have :X (r,c)•(single c (1:ℂ):Fq->ℂ)=af r X:=by
    ext j;by_cases hj:j=c
    .subst hj;simp[bu]
    .simp[bu,hj,(q j hj).1]
   rw[this];exact C4 P
 have T:=LZ L G r;have U:=LZ L G s
 obtain⟨a,ha⟩:∃ a:Fq,(single a (1:ℂ):Fq->ℂ)∉ k:=by
  by_contra h;push_neg at h;exact T (M5 k h)
 obtain⟨b,Q⟩:∃ b:Fq,(single b (1:ℂ):Fq->ℂ)∉ l:=by
  by_contra h;push_neg at h;exact U (M5 l h)
 have J:(single a (1:ℂ):Fq->ℂ)∈l:=(step1 a).resolve_left ha;have aj:(single b (1:ℂ):Fq->ℂ)∈k:=(step1 b).resolve_right Q
 have D:a≠b:=by
  intro h;subst h;exact Q J
 obtain⟨e,f,Mr⟩:=ajr a b D;have M:∀ X,YN r s a b e f X=0->(∀ j,j≠a->j≠b->X (r,j)=0/\X (s,j)=0)/\
   X (r,a)=X (r,b)/\X (s,a)= - X (s,b):=by
  intro X hX;have A:=congrFun hX 0;have p:=congrFun hX 1;have g:=congrFun hX 2;have i:=congrFun hX 3;have B:=congrFun hX 4;have C:=congrFun hX 5;simp[YN]at A p g i B C
  refine⟨?_,by linear_combination A,by linear_combination p⟩
  intro j PE d;rcases Mr j with h | h | h | h
  .exact absurd h PE
  .exact absurd h d
  .subst h;exact⟨g,B⟩
  .subst h;exact⟨i,C⟩
 have al:∀ X,YN r s a b e f X=0->p4 X=0:=by
  intro X hX;obtain⟨n,m,y⟩:=M X hX;apply Pd r s S X;intro u z F;by_cases o:u=a\/u=b
  .by_cases hd1:z=a\/z=b
   .rcases o with o | o<;>rcases hd1 with hd1 | hd1<;>subst o<;>subst hd1
    .exact absurd rfl F
    .rw[m,y];ring
    .rw[m,y];ring
    .exact absurd rfl F
   .push_neg at hd1;have :=n z hd1.1 hd1.2;rw[this.1,this.2];ring
  .push_neg at o;have :=n u o.1 o.2;rw[this.1,this.2];ring
 have hm:=Zx L G V (YN r s a b e f) al
 obtain⟨Y,ag,ae⟩:=dk (K:=L ⊓ ker (YN r s a b e f)) (by omega)
 obtain⟨N,ai⟩:=A6.1 ag;obtain⟨n,m,y⟩:=M Y (C7.1 ai);by_cases v:Y (r,b)=0
 .by_cases w:Y (s,b)=0
  .apply ae;apply H Y N
   .intro j;by_cases PE:j=a
    .subst PE;rw[m,v]
    .by_cases d:j=b
     .subst d;exact v
     .exact (n j PE d).1
   .intro j;by_cases PE:j=a
    .subst PE;rw[y,w];ring
    .by_cases d:j=b
     .subst d;exact w
     .exact (n j PE d).2
  .apply Q;have x:af s Y∈l:=C4 N
   have E:af s Y=Y (s,b)•((single b (1:ℂ):Fq->ℂ)-(single a (1:ℂ):Fq->ℂ)):=by
    ext j;by_cases PE:j=a
    .subst PE;simp[bu,D,y]
    .by_cases d:j=b
     .subst d;simp[bu,PE]
     .simp[bu,PE,d,(n j PE d).2]
   rw[E]at x;have g:=Ir l _ _ w x;have i:=l.add_mem g J;simpa using i
 .apply ha;have x:af r Y∈k:=C4 N
  have E:af r Y=Y (r,b)•((single a (1:ℂ):Fq->ℂ)+(single b (1:ℂ):Fq->ℂ)):=by
   ext j;by_cases PE:j=a
   .subst PE;simp[bu,D,m]
   .by_cases d:j=b
    .subst d;simp[bu,PE]
    .simp[bu,PE,d,(n j PE d).1]
  rw[E]at x;have g:=Ir k _ _ v x;have i:=k.sub_mem g aj;simpa using i
def ady (L:Sq) (a:∀ t∈L,p4 (Bm+ t)=65) (Y:Mt)
  (e:Y∈L ⊔ span ℂ {Bm}) (X:Mt) (d:X∈L):p4 (Y+ X)=p4 Y:=by
 obtain⟨t,b,m,f,rfl⟩:=C5.1 e;obtain⟨c,rfl⟩:=C6.1 f
 rw[show t+ c•Bm+ X=c•Bm+(t+ X) by abel,show t+ c•Bm=c•Bm+ t by abel,
  Ud L a _ (L.add_mem b d) c,Ud L a t b c]
lemma Ko (L:Sq) (a:∀ t∈L,p4 (Bm+ t)=65) (Y:Mt)
  (c:Y∈L ⊔ span ℂ {Bm}) (X:Mt) (b:X∈L) (k:ℂ):p4 (Y+ k•X)=p4 Y:=
 ady L a Y c (k•X) (L.smul_mem k b)
def PV (g a e h i f b c d:ℂ):ℂ:=
 g*i*d+ g*f*c+ a*h*d+ a*f*b+ e*h*c+ e*i*b
def m3 (r c:Fq) (X:Mt):ℂ:=
 PV (X (r+1,c+1)) (X (r+1,c+2)) (X (r+1,c+3)) (X (r+2,c+1)) (X (r+2,c+2)) (X (r+2,c+3))
  (X (r+3,c+1)) (X (r+3,c+2)) (X (r+3,c+3))
def ajd (r:Fq) (Y X:Mt) (a:∀ j,X (r,j)=0):
  p4 (Y+(3:ℂ)•X)-3*p4 (Y+(2:ℂ)•X)+3*p4 (Y+(1:ℂ)•X)- p4 Y
   =6* ∑ c:Fq,Y (r,c)*m3 r c X:=by
 have b:=a 0;have d:=a 1;have e:=a 2;have f:=a 3;fin_cases r<;>simp_all[p4,m3,PV,C2]<;>ring
lemma UF (L:Sq) (d:∀ t∈L,p4 (Bm+ t)=65) (r:Fq)
  (b:finrank ℂ (L.map (af r))=3):(L ⊔ span ℂ {Bm}).map (af r)= ⊤ :=by
 have c:af r Bm∉ L.map (af r):=by
  intro h;obtain⟨t,e,a⟩:=B6.1 h
  exact WJ L d r t e (λj=> by rw[<- bu r t j,a,bu])
 rw[Submodule.map_sup,O4,O6];apply M1;rw[du _ _ c,b];simp
lemma VE (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65) (r:Fq)
  (h:finrank ℂ (L.map (af r))=3) (X:Mt) (Px:X∈L) (i:∀ j,X (r,j)=0) (c:Fq):
  m3 r c X=0:=by
 have e:=UF L b r h
 have hc:(single c (1:ℂ):Fq->ℂ)∈(L ⊔ span ℂ {Bm}).map (af r):=by
  rw[e];trivial
 obtain⟨Y,hY,g⟩:=B6.1 hc;have a:=ajd r Y X i;rw[Ko L b Y hY X Px,Ko L b Y hY X Px,Ko L b Y hY X Px]at a
 have f:∀ d,Y (r,d)=(single c (1:ℂ):Fq->ℂ) d:=by
  intro d;rw[<- g,bu]
 simp only[f,C2]at a;fin_cases c<;>simp[]at a ⊢ <;>
  first | exact a | grind
def Wm (t u:Fq) (X:Mt) (c d:Fq):ℂ:=
 if c=d then 0 else ∑ a:Fq,∑ b:Fq,
  if a≠b/\a≠c/\a≠d/\b≠c/\b≠d then X (t,a)*X (u,b) else 0
def af5 (t u:Fq) (X:Mt) (c:Fq):Wm t u X c c=0:=by simp[Wm]
def af6 (t u:Fq) (X:Mt) (c d:Fq):Wm t u X c d=Wm t u X d c:=by
 unfold Wm;by_cases h:c=d
 .subst h;rfl
 .rw[C9 h,C9 (Ne.symm h)];apply K3 rfl;intro a _;apply K3 rfl;intro b _;apply if_congr _ rfl rfl;constructor<;>rintro⟨h1,e,f,g,i⟩<;>exact⟨h1,f,e,i,g⟩
def MH:(∀ (Y X:Mt) (a:∀ j,X (0,j)=0) (b:∀ j,X (1,j)=0),p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=2* ∑ c:Fq,∑ d:Fq,Y (0,c)*Wm 2 3 X c d*Y (1,d))/\(∀ (Y X:Mt) (a:∀ j,X (0,j)=0) (b:∀ j,X (2,j)=0),p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=2* ∑ c:Fq,∑ d:Fq,Y (0,c)*Wm 1 3 X c d*Y (2,d))/\(∀ (Y X:Mt) (a:∀ j,X (0,j)=0) (b:∀ j,X (3,j)=0),p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=2* ∑ c:Fq,∑ d:Fq,Y (0,c)*Wm 1 2 X c d*Y (3,d))/\(∀ (Y X:Mt) (a:∀ j,X (1,j)=0) (b:∀ j,X (2,j)=0),p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=2* ∑ c:Fq,∑ d:Fq,Y (1,c)*Wm 0 3 X c d*Y (2,d))/\(∀ (Y X:Mt) (a:∀ j,X (1,j)=0) (b:∀ j,X (3,j)=0),p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=2* ∑ c:Fq,∑ d:Fq,Y (1,c)*Wm 0 2 X c d*Y (3,d))/\(∀ (Y X:Mt) (a:∀ j,X (2,j)=0) (b:∀ j,X (3,j)=0),p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=2* ∑ c:Fq,∑ d:Fq,Y (2,c)*Wm 0 1 X c d*Y (3,d)):=by
 refine⟨?_,?_,?_,?_,?_,?_⟩<;>intro Y X a b;all_goals
  have i:=a 0;have k:=a 1;have l:=a 2;have m:=a 3
  have e:=b 0;have f:=b 1;have g:=b 2;have h:=b 3
  simp only[p4,Wm,C2,A1,A4,A5]
  simp only[i,k,l,m,e,f,g,h]
  norm_num
  ring
def abF:∀ r s t u:Fq,r< s->t< u->r≠t->r≠u->s≠t->s≠u->
  (r=0/\s=1/\t=2/\u=3)\/(r=0/\s=2/\t=1/\u=3)\/(r=0/\s=3/\t=1/\u=2)\/
  (r=1/\s=2/\t=0/\u=3)\/(r=1/\s=3/\t=0/\u=2)\/(r=2/\s=3/\t=0/\u=1):=by
 intro r s t u;fin_cases r<;>fin_cases s<;>fin_cases t<;>fin_cases u<;>decide
def aph (r s t u:Fq) (e:r< s) (f:t< u) (g:r≠t) (h:r≠u) (i:s≠t) (h6:s≠u)
  (Y X:Mt) (a:∀ j,X (r,j)=0) (b:∀ j,X (s,j)=0):
  p4 (Y+(2:ℂ)•X)-2*p4 (Y+(1:ℂ)•X)+ p4 Y=
   2* ∑ c:Fq,∑ d:Fq,Y (r,c)*Wm t u X c d*Y (s,d):=by
 rcases abF r s t u e f g h i h6 with⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
  ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
 .exact MH.1 Y X a b
 .exact MH.2.1 Y X a b
 .exact MH.2.2.1 Y X a b
 .exact MH.2.2.2.1 Y X a b
 .exact MH.2.2.2.2.1 Y X a b
 .exact MH.2.2.2.2.2 Y X a b
def Qr (U:Submodule ℂ (Fq->ℂ)) (h:U≠ ⊤):
  ∃ a:Fq,(single a (1:ℂ):Fq->ℂ)∉ U:=by
 by_contra hc;push_neg at hc;exact h (M5 U hc)
lemma O8 (f:Fq->ℂ) (e:Fq):
  ∑ c:Fq,(single e (1:ℂ):Fq->ℂ) c*f c=f e:=by
 simp[C1]
def R6 (W:Fq->Fq->ℂ) (U:Submodule ℂ (Fq->ℂ)): Prop :=
 ∀ v∈U,∀ e,∑ d:Fq,W e d*v d=0
def aec (W:Fq->Fq->ℂ) (U V:Submodule ℂ (Fq->ℂ)) (c:R6 W U) (d:R6 W V):
  R6 W (U ⊔ V):=by
 intro v hv e;obtain⟨x,hx,y,f,rfl⟩:=C5.1 hv;have a:=c x hx e;have b:=d y f e;simp only[A1,F7,E8,a,b,B8]
lemma RH (W:Fq->Fq->ℂ) (e d:Fq):
  W e d= ∑ j:Fq,W e j*(single d (1:ℂ):Fq->ℂ) j:=by
 simp[C1]
def aa1 (W:Fq->Fq->ℂ) (a:R6 W ⊤):∀ e d,W e d=0:=by
 intro e d;rw[RH W e d];exact a _ trivial e
def Ym (W:Fq->Fq->ℂ) (l:∀ c d,W c d=W d c) (k:∀ c,W c c=0)
  (U:Submodule ℂ (Fq->ℂ)) (i:R6 W U) (a:Fq)
  (h:U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)}= ⊤):∀ c d,W c d=0:=by
 have j:∀ e,W e a=0:=by
  intro e
  have hm:(single e (1:ℂ):Fq->ℂ)∈U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)}:=by
   rw[h];trivial
  obtain⟨x,f,y,g,Zq⟩:=C5.1 hm;obtain⟨m,rfl⟩:=C6.1 g;have b:=i x f a;rw[l,RH W a e,<- Zq];simp only[A1,A4,A5,F7,E8,b,C0];simp[C1,k]
 intro c d
 have hm:(single d (1:ℂ):Fq->ℂ)∈U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)}:=by
  rw[h];trivial
 obtain⟨x,f,y,g,Zq⟩:=C5.1 hm;obtain⟨m,rfl⟩:=C6.1 g;have b:=i x f c;rw[RH W c d,<- Zq];simp only[A1,A4,A5,F7,E8,b,C0];simp[C1,j c]
def Yn (W:Fq->Fq->ℂ) (l:∀ c d,W c d=W d c) (k:∀ c,W c c=0)
  (U:Submodule ℂ (Fq->ℂ)) (j:R6 W U) (a b:Fq) (h:W a b=0)
  (p:U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)} ⊔
   span ℂ {(single b (1:ℂ):Fq->ℂ)}= ⊤):∀ c d,W c d=0:=by
 have o:W b a=0:=by rw[l];exact h
 have g:∀ v:Fq->ℂ,∃ x∈U,∃ α β:ℂ,v=x+ α•(single a (1:ℂ):Fq->ℂ)+
   β•(single b (1:ℂ):Fq->ℂ):=by
  intro v;have s:v∈U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)} ⊔
    span ℂ {(single b (1:ℂ):Fq->ℂ)}:=by rw[p];trivial
  obtain⟨w,q,z,u,rfl⟩:=C5.1 s;obtain⟨x,hx,y,t,rfl⟩:=C5.1 q;obtain⟨α,rfl⟩:=C6.1 t;obtain⟨β,rfl⟩:=C6.1 u;exact⟨x,hx,α,β,rfl⟩
 have f:∀ e,W a e=0/\W b e=0:=by
  intro e;obtain⟨x,hx,α,β,hv⟩:=g (single e (1:ℂ));have i:=j x hx a;have r:=j x hx b;constructor
  .rw[RH W a e,hv];simp only[A1,A4,A5,F7,E8,i,C0];simp[C1,k,h]
  .rw[RH W b e,hv];simp only[A1,A4,A5,F7,E8,r,C0];simp[C1,k,o]
 intro c d;obtain⟨x,hx,α,β,hv⟩:=g (single d (1:ℂ));have i:=j x hx c;rw[RH W c d,hv];simp only[A1,A4,A5,F7,E8,i,C0];have m:=(f c).1;have n:=(f c).2;rw[l]at m n;simp[C1,m,n]
def RY (f:Fq->ℂ) (a:Fq):
  ∑ d:Fq,f d*(single a (1:ℂ):Fq->ℂ) d=f a:=by
 simp[C1]
lemma ac9 (W:Fq->Fq->ℂ) (r s:Fq) (Y Z:Mt) (a:∀ j,Z (r,j)=0):
  ∑ c:Fq,∑ d:Fq,(Y+ Z) (r,c)*W c d*(Y+ Z) (s,d)=
   ∑ c:Fq,∑ d:Fq,Y (r,c)*W c d*Y (s,d)+
    ∑ c:Fq,Y (r,c)* ∑ d:Fq,W c d*Z (s,d):=by
 simp only[C2,A1,a];ring
lemma abI (W:Fq->Fq->ℂ) (r s:Fq) (Y Z:Mt) (a:∀ j,Z (s,j)=0):
  ∑ c:Fq,∑ d:Fq,(Y+ Z) (r,c)*W c d*(Y+ Z) (s,d)=
   ∑ c:Fq,∑ d:Fq,Y (r,c)*W c d*Y (s,d)+
    ∑ d:Fq,Y (s,d)* ∑ c:Fq,Z (r,c)*W c d:=by
 simp only[C2,A1,a];ring
lemma ada (W:Fq->Fq->ℂ) (r s:Fq) (Y:Mt) (x a b:Fq) (α e:ℂ)
  (g:∀ c,Y (r,c)=(single x (1:ℂ):Fq->ℂ) c)
  (h:∀ d,Y (s,d)= α*(single a (1:ℂ):Fq->ℂ) d+ e*(single b (1:ℂ):Fq->ℂ) d):
  ∑ c:Fq,∑ d:Fq,Y (r,c)*W c d*Y (s,d)= α*W x a+ e*W x b:=by
 have f:∀ c,∑ d:Fq,Y (r,c)*W c d*Y (s,d)=
   (single x (1:ℂ):Fq->ℂ) c*(α*W c a+ e*W c b):=by
  intro c;simp only[g,h,F7,E8]
  have :=RY (λd=> W c d) a
  have :=RY (λd=> W c d) b
  simp only[C1];simp;ring
 simp only[f]
 exact O8 (λc=> α*W c a+ e*W c b) x
def Tk (r s:Fq) (f:r≠s) (Y:Mt) (a:Fq)
  (hr:∀ c,c≠a->Y (r,c)=0) (e:∀ c,c≠a->Y (s,c)=0):p4 Y=0:=by
 apply Pd r s f Y;intro c d b;by_cases hc:c=a
 .subst hc;rw[hr d (Ne.symm b),e d (Ne.symm b)];ring
 .rw[hr c hc,e c hc];ring
def N1 (L:Sq) (o:∀ t∈L,p4 (Bm+ t)=65) (h6:finrank ℂ L=6)
  (r s t u:Fq) (h1:r< s) (O:t< u) (h3:r≠t) (h4:r≠u) (h5:s≠t) (Lx:s≠u)
  (U0:finrank ℂ (L.map (af r))=3) (aK:finrank ℂ (L.map (af s))=3)
  (X:Mt) (Px:X∈L) (ae:∀ j,X (r,j)=0) (ag:∀ j,X (s,j)=0) (OT:X≠0)
  (Nh:∀ Y∈L,(∀ j,Y (r,j)=0)->(∀ j,Y (s,j)=0)-> ∃ c:ℂ,Y=c•X):
  ∀ c d,Wm t u X c d=0:=by
 have PH:r≠s:=D5 h1;set W:=Wm t u X with hW
 have N:∀ c d,W c d=W d c:=λc d=> af6 t u X c d
 have M:∀ c,W c c=0:=λc=> af5 t u X c
 set C:=L ⊔ span ℂ {Bm} with hC;have D:L≤ C:=K8
 have f:∀ Y∈C,∑ c:Fq,∑ d:Fq,Y (r,c)*W c d*Y (s,d)=0:=by
  intro Y hY;have aP:=aph r s t u h1 O h3 h4 h5 Lx Y X ae ag;rw[Ko L o Y hY X Px,Ko L o Y hY X Px]at aP;grind
 have ao:∀ Z∈L,(∀ j,Z (r,j)=0)-> ∀ e,∑ d:Fq,W e d*Z (s,d)=0:=by
  intro Z i LQ e
  have hc:(single e (1:ℂ):Fq->ℂ)∈C.map (af r):=by rw[UF L o r U0];trivial
  obtain⟨Y,hY,Vl⟩:=B6.1 hc
  have OU:∀ c,Y (r,c)=(single e (1:ℂ):Fq->ℂ) c:=λc=> by rw[<- Vl,bu]
  have k:=f (Y+ Z) (C.add_mem hY (D i));have sB:=f Y hY;rw[ac9 W r s Y Z LQ,sB,C0]at k;simp only[OU]at k
  rw[O8 (λc=> ∑ d:Fq,W c d*Z (s,d)) e]at k
  exact k
 have am:∀ Z∈L,(∀ j,Z (s,j)=0)-> ∀ e,∑ d:Fq,W e d*Z (r,d)=0:=by
  intro Z i G e
  have hc:(single e (1:ℂ):Fq->ℂ)∈C.map (af s):=by rw[UF L o s aK];trivial
  obtain⟨Y,hY,Vl⟩:=B6.1 hc
  have Zd:∀ c,Y (s,c)=(single e (1:ℂ):Fq->ℂ) c:=λc=> by rw[<- Vl,bu]
  have k:=f (Y+ Z) (C.add_mem hY (D i));have sB:=f Y hY;rw[abI W r s Y Z G,sB,C0]at k;simp only[Zd]at k
  rw[O8 (λd=> ∑ c:Fq,Z (r,c)*W c d) e]at k
  have : ∑ d:Fq,W e d*Z (r,d)= ∑ c:Fq,Z (r,c)*W c e:=by
   apply K3 rfl;intro d _;rw[N];ring
  rw[this];exact k
 have aT:finrank ℂ ↥(L ⊓ ker (af r))=3:=by
  have :=dx L (af r);omega
 have aU:finrank ℂ ↥(L ⊓ ker (af s))=3:=by
  have :=dx L (af s);omega
 have al:∀ K:Sq,K≤ L ⊓ ker (af r) ⊓ ker (af s)->
   X∈K->(∀ Y∈K,Y∈L/\(∀ j,Y (r,j)=0)/\(∀ j,Y (s,j)=0))->finrank ℂ K=1:=by
  intro K _ aH ap
  have aI:K=span ℂ {X}:=by
   apply le_antisymm
   .intro Y hY;obtain⟨I2,OU,Zd⟩:=ap Y hY;obtain⟨c,rfl⟩:=Nh Y I2 OU Zd;exact D6 _ c (P0 X)
   .rw[M2];intro Y hY;rw[Set.mem_singleton_iff]at hY;rw[hY];exact aH
  rw[aI,O3 OT]
 have J:∀ Y,Y∈L ⊓ ker (af r) ⊓ ker (af s)↔
   Y∈L/\(∀ j,Y (r,j)=0)/\(∀ j,Y (s,j)=0):=by
  intro Y;simp only[A6,C7];constructor
  .rintro⟨⟨hY,hr⟩,hs⟩
   exact⟨hY,λj=> by have :=congrFun hr j;simpa[bu] using this,
    λj=> by have :=congrFun hs j;simpa[bu] using this⟩
  .rintro⟨hY,hr,hs⟩
   exact⟨⟨hY,funext λj=> by simp[bu,hr j]⟩,funext λj=> by simp[bu,hs j]⟩
 have aF:finrank ℂ ↥(L ⊓ ker (af r) ⊓ ker (af s))=1:=
  al _ le_rfl ((J X).2 ⟨Px,ae,ag⟩) (λY hY=>(J Y).1 hY)
 have aQ:finrank ℂ ↥(L ⊓ ker (af s) ⊓ ker (af r))=1:=by
  rw[inf_assoc,inf_comm (ker (af s)),<- inf_assoc];exact aF
 obtain⟨q,Zb⟩:∃ V:Submodule ℂ (Fq->ℂ),V=(L ⊓ ker (af r)).map (af s):=
  ⟨_,rfl⟩
 obtain⟨n,Za⟩:∃ V:Submodule ℂ (Fq->ℂ),V=(L ⊓ ker (af s)).map (af r):=
  ⟨_,rfl⟩
 have aC:finrank ℂ q=2:=by
  rw[Zb];have :=dx (L ⊓ ker (af r)) (af s);omega
 have aA:finrank ℂ n=2:=by
  rw[Za];have :=dx (L ⊓ ker (af s)) (af r);omega
 have aO:R6 W q:=by
  intro v hv e;rw[Zb]at hv;obtain⟨Z,F,rfl⟩:=B6.1 hv;obtain⟨i,Us⟩:=A6.1 F
  have LQ:∀ j,Z (r,j)=0:=λj=> by
   have :=congrFun (C7.1 Us) j;simpa[bu] using this
  simpa[bu] using ao Z i LQ e
 have aN:R6 W n:=by
  intro v hv e;rw[Za]at hv;obtain⟨Z,F,rfl⟩:=B6.1 hv;obtain⟨i,Us⟩:=A6.1 F
  have G:∀ j,Z (s,j)=0:=λj=> by
   have :=congrFun (C7.1 Us) j;simpa[bu] using this
  simpa[bu] using am Z i G e
 obtain⟨U,w⟩:∃ U:Submodule ℂ (Fq->ℂ),U=n ⊔ q:=⟨_,rfl⟩
 have P:R6 W U:=by rw[w];exact aec W n q aN aO
 have R:q≤ U:=by rw[w];exact le_sup_right
 have aB:n≤ U:=by rw[w];exact K8
 have as:n≤ L.map (af r):=by rw[Za];exact P5 inf_le_left
 by_cases T:U= ⊤
 .rw[T]at P;exact aa1 W P
 obtain⟨a,ha⟩:=Qr U T;obtain⟨g,YZ⟩:∃ g:Submodule ℂ (Fq->ℂ),
   g=U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)}:=⟨_,rfl⟩
 by_cases A:g= ⊤
 .rw[YZ]at A;exact Ym W N M U P a A
 obtain⟨b,hb⟩:=Qr g A
 have aw:finrank ℂ g=finrank ℂ U+1:=by rw[YZ];exact du U _ ha
 have ax:finrank ℂ ↥(g ⊔ span ℂ {(single b (1:ℂ):Fq->ℂ)})=finrank ℂ g+1:=
  du g _ hb
 have aS:finrank ℂ ↥(g ⊔ span ℂ {(single b (1:ℂ):Fq->ℂ)})≤4:=by
  have :=H4 (g ⊔ span ℂ {(single b (1:ℂ):Fq->ℂ)});simpa using this
 have aR:2≤ finrank ℂ U:=by
  have :=E7 R;omega
 have E:finrank ℂ U=2:=by omega
 have az:U=q:=(M3 R (by rw[aC,E])).symm
 have ay:U=n:=(M3 aB (by rw[aA,E])).symm
 have abl:U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)} ⊔
   span ℂ {(single b (1:ℂ):Fq->ℂ)}= ⊤ :=by
  rw[<- YZ];apply M1;rw[ax,aw,E,M7]
 by_contra od;push_neg at od;obtain⟨c0,d0,au⟩:=od
 have ai:W a b≠0:=by
  intro h0;exact au (Yn W N M U P a b h0 abl c0 d0)
 have aE:∀ v:Fq->ℂ,∃ x∈U,∃ l m:ℂ,v=x+ l•(single a (1:ℂ):Fq->ℂ)+
   m•(single b (1:ℂ):Fq->ℂ):=by
  intro v;have hm:v∈U ⊔ span ℂ {(single a (1:ℂ):Fq->ℂ)} ⊔
    span ℂ {(single b (1:ℂ):Fq->ℂ)}:=by rw[abl];trivial
  obtain⟨xy,Zq,z,hz,rfl⟩:=C5.1 hm;obtain⟨x,hx,y,hy,rfl⟩:=C5.1 Zq;obtain⟨l,rfl⟩:=C6.1 hy;obtain⟨m,rfl⟩:=C6.1 hz;exact⟨x,hx,l,m,rfl⟩
 have Q:∀ x:Fq,(x=a\/x=b)->(single x (1:ℂ):Fq->ℂ)∈L.map (af r):=by
  intro x hx
  have hc:(single x (1:ℂ):Fq->ℂ)∈C.map (af r):=by rw[UF L o r U0];trivial
  obtain⟨Y,hY,Vl⟩:=B6.1 hc;obtain⟨v,aj,l,m,av⟩:=aE (af s Y);rw[az,Zb]at aj;obtain⟨Z,F,aD⟩:=B6.1 aj;obtain⟨i,Us⟩:=A6.1 F
  have LQ:∀ j,Z (r,j)=0:=λj=> by
   have :=congrFun (C7.1 Us) j;simpa[bu] using this
  set h:=Y- Z with Mp;have S:h∈C:=C.sub_mem hY (D i)
  have p:∀ c,h (r,c)=(single x (1:ℂ):Fq->ℂ) c:=by
   intro c;simp only[Mp,G3,LQ,sub_zero]
   rw[show Y (r,c)=af r Y c from rfl,Vl]
  have B:∀ d,h (s,d)=l*(single a (1:ℂ):Fq->ℂ) d+ m*(single b (1:ℂ):Fq->ℂ) d:=by
   intro d;have h1:=congrFun av d;have O:=congrFun aD d;simp only[bu]at h1 O;simp only[Mp,G3,h1,<- O,A1,A4,A5];ring
  have H:=f h S;rw[ada W r s h x a b l m p B]at H
  have aJ:p4 h=0:=by
   rcases hx with rfl | rfl
   .have aM:m=0:=by
     rw[M x]at H
     have :m*W x b=0:=by grind
     exact (A0.1 this).resolve_right ai
    apply Tk r s PH h x
    .intro c hc;rw[p c];simp[hc]
    .intro c hc;rw[B c,aM];simp[C1,hc]
   .have aL:l=0:=by
     rw[M x,N x a]at H
     have :l*W a x=0:=by grind
     exact (A0.1 this).resolve_right ai
    apply Tk r s PH h x
    .intro c hc;rw[p c];simp[hc]
    .intro c hc;rw[B c,aL];simp[C1,hc]
  have LJ:=fk L o h S aJ
  have :af r h=(single x (1:ℂ):Fq->ℂ):=by ext c;rw[bu,p c]
  rw[<- this];exact C4 LJ
 have aG:L.map (af r)= ⊤ :=by
  rw[eq_top_iff,<- abl];apply sup_le
  .apply sup_le
   .rw[ay];exact as
   .rw[M2,P6];exact Q a (Or.inl rfl)
  .rw[M2,P6];exact Q b (Or.inr rfl)
 exact LZ L o r aG
lemma WA (X:Mt):p4 X=permanent (Matrix.of λ(i j:Fq)=> X (i,j)):=by
 rw[afC];simp[p4,Matrix.of_apply]
lemma Xr (M:Matrix Fq Fq ℂ) (e:Equiv.Perm Fq):
  (M.submatrix e e).permanent=M.permanent:=by
 simp only[permanent,Matrix.submatrix_apply];symm;rw[<- (Equiv.permCongr e).sum_comp];apply K3 rfl;intro a _;rw[<- Equiv.prod_comp e];apply Finset.prod_congr rfl;intro i _;simp[]
def act (a:Equiv.Perm Fq) (X:Mt):Mt:=λq=> X (a.symm q.1,a.symm q.2)
def gp (a:Equiv.Perm Fq):Mt→ₗ[ℂ] Mt where
 toFun:=act a
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma my (a:Equiv.Perm Fq) (X:Mt) (i j:Fq):
  gp a X (i,j)=X (a.symm i,a.symm j):=rfl
lemma ajv (a:Equiv.Perm Fq) (X:Mt):p4 (gp a X)=p4 X:=by
 rw[WA,WA]
 have :(Matrix.of λ(i j:Fq)=> gp a X (i,j))=
   (Matrix.of λ(i j:Fq)=> X (i,j)).submatrix a.symm a.symm:=by
  ext i j;simp[my]
 rw[this,Xr]
lemma acf (a:Equiv.Perm Fq):gp a Bm=Bm:=by
 ext ⟨i,j⟩;simp only[my,Bm];simp[a.symm.injective.eq_iff]
lemma LY (L:Sq) (c:∀ t∈L,p4 (Bm+ t)=65) (a:Equiv.Perm Fq):
  ∀ t∈L.map (gp a),p4 (Bm+ t)=65:=by
 intro t d;obtain⟨e,b,rfl⟩:=B6.1 d;rw[<- acf a,<- E9,ajv];exact c e b
def O5 (a:Equiv.Perm Fq):Function.Injective (gp a):=by
 intro X Y h;ext ⟨i,j⟩;have :=congrFun h (a i,a j);simpa[my] using this
lemma o6 (L:Sq) (a:Equiv.Perm Fq):
  finrank ℂ (L.map (gp a))=finrank ℂ L:=
 K2 (equivMapOfInjective _ (O5 a) L) |>.symm
def Mv:Mt→ₗ[ℂ] Mt where
 toFun X:=λq=> X (q.2,q.1)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma Mw (X:Mt) (i j:Fq):Mv X (i,j)=X (j,i):=rfl
lemma afB (X:Mt):p4 (Mv X)=p4 X:=by
 simp only[p4,Mw];ring
lemma afM:Mv Bm=Bm:=by
 ext ⟨i,j⟩;simp only[Mw,Bm];by_cases h:i=j
 .subst h;simp
 .simp[h,Ne.symm h]
lemma QR (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65):
  ∀ t∈L.map Mv,p4 (Bm+ t)=65:=by
 intro t c;obtain⟨d,a,rfl⟩:=B6.1 c;rw[<- afM,<- E9,afB];exact b d a
def agq:Function.Injective Mv:=by
 intro X Y h;ext ⟨i,j⟩;have :=congrFun h (j,i);simpa[Mw] using this
lemma Qv (L:Sq):finrank ℂ (L.map Mv)=finrank ℂ L:=
 K2 (equivMapOfInjective _ agq L) |>.symm
def ZR (x y:Fq->ℂ) (h:∀ c d:Fq,c≠d->x c*y d+ x d*y c=0)
  (c:Fq) (l:x c≠0) (o:∃ j,y j≠0):
  y c≠0/\(∀ d:Fq,d≠c->x c*y d= -(x d*y c))/\
  (∀ d e:Fq,d≠c->e≠c->d≠e->x d*x e=0):=by
 have g:y c≠0:=by
  intro i;obtain⟨j,n⟩:=o;apply n;by_cases a:j=c
  .subst a;exact i
  .have :=h c j (Ne.symm a);rw[i,C3,B8]at this;exact (A0.1 this).resolve_left l
 refine⟨g,?_,?_⟩
 .intro d f;have :=h c d (Ne.symm f);grind
 .intro d e f m hde;have p:=h c d (Ne.symm f);have q:=h c e (Ne.symm m);have r:=h d e hde
  have k:x d*x e*(2*y c)=0:=by
   grind
  rcases A0.1 k with b | b
  .exact b
  .exfalso;apply g;have :(2:ℂ)*y c=0:=b;simpa using this
def Z8 (t u:Fq) (X:Mt) (a:∀ c d,Wm t u X c d=0):
  ∀ c d:Fq,c≠d->X (t,c)*X (u,d)+ X (t,d)*X (u,c)=0:=by
 intro c d b;fin_cases c<;>fin_cases d<;>simp at b
 .have h:=a 2 3;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,0)*X (u,1)+ X (t,1)*X (u,0)=0)
 .have h:=a 1 3;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,0)*X (u,2)+ X (t,2)*X (u,0)=0)
 .have h:=a 1 2;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,0)*X (u,3)+ X (t,3)*X (u,0)=0)
 .have h:=a 2 3;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,1)*X (u,0)+ X (t,0)*X (u,1)=0)
 .have h:=a 0 3;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,1)*X (u,2)+ X (t,2)*X (u,1)=0)
 .have h:=a 0 2;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,1)*X (u,3)+ X (t,3)*X (u,1)=0)
 .have h:=a 1 3;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,2)*X (u,0)+ X (t,0)*X (u,2)=0)
 .have h:=a 0 3;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,2)*X (u,1)+ X (t,1)*X (u,2)=0)
 .have h:=a 0 1;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,2)*X (u,3)+ X (t,3)*X (u,2)=0)
 .have h:=a 1 2;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,3)*X (u,0)+ X (t,0)*X (u,3)=0)
 .have h:=a 0 2;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,3)*X (u,1)+ X (t,1)*X (u,3)=0)
 .have h:=a 0 1;simp[Wm,C2]at h
  exact (by linear_combination h:X (t,3)*X (u,2)+ X (t,2)*X (u,3)=0)
def Ar (L:Sq) (r:Fq):Sq:=L ⊓ ker (af r)
lemma ei (L:Sq) (r:Fq) (X:Mt):
  X∈Ar L r↔X∈L/\ ∀ j,X (r,j)=0:=by
 unfold Ar;rw[A6,C7];constructor
 .rintro⟨a,b⟩
  exact⟨a,λj=> by have :=congrFun b j;simpa[bu] using this⟩
 .rintro⟨a,b⟩
  exact⟨a,by ext j;simp[bu,b j]⟩
lemma MF (L:Sq) (a:finrank ℂ L=6) (r:Fq)
  (b:finrank ℂ (L.map (af r))=3):finrank ℂ (Ar L r)=3:=by
 have :=dx L (af r);unfold Ar;omega
lemma I6 (L:Sq) (r:Fq):Ar L r≤ L:=inf_le_left
def Uy (A a b:Sq) (e:finrank ℂ A=3) (c:a≤ A) (d:b≤ A)
  (f:2≤ finrank ℂ a) (g:2≤ finrank ℂ b):∃ X∈a ⊓ b,X≠0:=by
 have h:finrank ℂ ↥(a ⊔ b)≤3:=by
  rw[<- e];exact E7 (sup_le c d)
 have :=H3 a b
 exact dk (by omega)
def LU (P:Submodule ℂ (Fq->ℂ)) (hP:finrank ℂ P≤1)
  (x y:Fq->ℂ) (f:x∈P) (g:y∈P) (c d:Fq):x c*y d=x d*y c:=by
 obtain⟨v,hv⟩:=(finrank_le_one_iff (K:= ℂ) (V:=P)).1 hP;obtain⟨a,ha⟩:=hv ⟨x,f⟩;obtain⟨b,e⟩:=hv ⟨y,g⟩
 have ex:x=a•(v:Fq->ℂ):=by
  have :=congrArg Subtype.val ha;simpa using this.symm
 have ey:y=b•(v:Fq->ℂ):=by
  have :=congrArg Subtype.val e;simpa using this.symm
 rw[ex,ey];simp only[A4,A5];ring
def Mc (t u c:Fq) (X:Mt): Prop :=
 (∀ i j,¬ ((i=t\/i=u)/\j=c)->X (i,j)=0)/\X (t,c)≠0/\X (u,c)≠0
def Ke (t u c d:Fq) (X:Mt): Prop :=
 (∀ i j,¬ ((i=t\/i=u)/\(j=c\/j=d))->X (i,j)=0)/\X (t,c)≠0/\X (t,d)≠0/\
  X (u,c)≠0/\X (u,d)≠0/\X (t,c)*X (u,d)+ X (t,d)*X (u,c)=0
def XH (t u:Fq) (F:t≠u) (X:Mt)
  (p:∀ i j,i≠t->i≠u->X (i,j)=0)
  (y:∀ c d:Fq,c≠d->X (t,c)*X (u,d)+ X (t,d)*X (u,c)=0)
  (D:∃ j,X (t,j)≠0) (E:∃ j,X (u,j)≠0):
  (∃ c,Mc t u c X)\/(∃ c d,c< d/\Ke t u c d X):=by
 obtain⟨c,k⟩:=D
 obtain⟨n,l,B⟩:=ZR (λj=> X (t,j)) (λj=> X (u,j)) y c k E
 by_cases m:∀ d,d≠c->X (t,d)=0
 .left;refine⟨c,?_,k,n⟩;intro i j b;by_cases a:i=t\/i=u
  .have hj:j≠c:=λh=> b ⟨a,h⟩
   rcases a with rfl | rfl
   .exact m j hj
   .have g:=l j hj;rw[m j hj,F4,neg_zero]at g;exact (A0.1 g).resolve_left k
  .push_neg at a;exact p i j a.1 a.2
 .right;push_neg at m;obtain⟨d,f,o⟩:=m
  have x:∀ e,e≠c->e≠d->X (t,e)=0/\X (u,e)=0:=by
   intro e r A;have g:=B d e f r (Ne.symm A);have s:X (t,e)=0:=(A0.1 g).resolve_left o;refine⟨s,?_⟩;have h2:=l e r;rw[s,F4,neg_zero]at h2;exact (A0.1 h2).resolve_left k
  have v:X (u,d)≠0:=by
   intro C;have h2:=l d f;rw[C,C3]at h2
   have :X (t,d)*X (u,c)=0:=by grind
   rcases A0.1 this with h3 | h3
   .exact o h3
   .exact n h3
  have q:∀ i j,¬ ((i=t\/i=u)/\(j=c\/j=d))->X (i,j)=0:=by
   intro i j b;by_cases a:i=t\/i=u
   .have hj:j≠c/\j≠d:=by
     constructor
     .intro h;exact b ⟨a,Or.inl h⟩
     .intro h;exact b ⟨a,Or.inr h⟩
    rcases a with rfl | rfl
    .exact (x j hj.1 hj.2).1
    .exact (x j hj.1 hj.2).2
   .push_neg at a;exact p i j a.1 a.2
  have z:=y c d (Ne.symm f);rcases lt_or_gt_of_ne f with w | w
  .refine⟨d,c,w,?_,o,k,v,n,?_⟩
   .intro i j b;apply q i j;rintro⟨g,h2⟩;exact b ⟨g,h2.symm⟩
   .grind
  .refine⟨c,d,w,q,k,o,n,v,z⟩
def E (i j:Fq):Mt:=λp=> if p.1=i/\p.2=j then 1 else 0
def M4 (t u c:Fq) (y:ℂ):Mt:=E t c+ y•E u c
def Q9 (t u c d:Fq) (q y:ℂ):Mt:=E t c+ q•E t d+ y•E u c+(-(q*y))•E u d
def VC (t u c:Fq) (g:t≠u) (X:Mt) (h:Mc t u c X):
  ∃ f y:ℂ,f≠0/\y≠0/\X=f•M4 t u c y:=by
 obtain⟨d,e,hu⟩:=h;refine⟨X (t,c),X (u,c)/X (t,c),e,L0 hu e,?_⟩;ext ⟨i,j⟩;simp only[M4,E,A1,A4,A5];by_cases hj:j=c
 .subst hj;by_cases b:i=t
  .subst b;simp[g]
  .by_cases a:i=u
   .subst a;simp[b];field_simp
   .rw[d i j (by rintro⟨h1 | h1,_⟩<;>contradiction)];simp[b,a]
 .rw[d i j (by rintro⟨_,h1⟩;exact hj h1)];simp[hj]
def Vy (t u c d:Fq) (f:t≠u) (Kx:c≠d) (X:Mt) (h:Ke t u c d X):
  ∃ m q y:ℂ,m≠0/\q≠0/\y≠0/\X=m•Q9 t u c d q y:=by
 obtain⟨g,htc,k,l,n,o⟩:=h;refine⟨X (t,c),X (t,d)/X (t,c),X (u,c)/X (t,c),htc,L0 k htc,
  L0 l htc,?_⟩
 have aoT:X (u,d)= -(X (t,d)*X (u,c))/X (t,c):=by
  field_simp;grind
 ext ⟨i,j⟩;simp only[Q9,E,A1,A4,A5];by_cases Wg:i=t
 .subst Wg;by_cases b:j=c
  .subst b;simp[f,Kx]
  .by_cases a:j=d
   .subst a;simp[f,b];field_simp
   .rw[g i j (by rintro⟨_,h1 | h1⟩<;>contradiction)];simp[b,a,f]
 .by_cases e:i=u
  .subst e;by_cases b:j=c
   .subst b;simp[Wg,Kx];field_simp
   .by_cases a:j=d
    .subst a;simp[Wg,b];rw[aoT];field_simp
    .rw[g i j (by rintro⟨_,h1 | h1⟩<;>contradiction)];simp[b,a,Wg]
  .rw[g i j (by rintro⟨h1 | h1,_⟩<;>contradiction)];simp[Wg,e]
def iz:Fin 10->Fq:= ![0,1,2,3,0,0,0,1,1,2]
def mr:Fin 10->Fq:= ![0,1,2,3,1,2,3,2,3,3]
def ot (t u:Fq) (a:Fin 10) (X:Mt): Prop :=
 if a.val<4 then Mc t u (iz a) X else Ke t u (iz a) (mr a) X
def Qx:∀ a:Fin 10,4≤ a.val->iz a≠mr a:=by decide
def SR (t u:Fq) (X:Mt)
  (h:(∃ c,Mc t u c X)\/(∃ c d,c< d/\Ke t u c d X)):∃ f,ot t u f X:=by
 rcases h with⟨c,e⟩ | ⟨c,d,b,a⟩
 .refine⟨⟨c.val,by omega⟩,?_⟩
  have hv:(⟨c.val,by omega⟩:Fin 10).val<4:=c.isLt
  simp only[ot,hv,A9]
  have :iz ⟨c.val,by omega⟩=c:=by fin_cases c<;>rfl
  rw[this];exact e
 .fin_cases c<;>fin_cases d<;>simp at b
  .exact⟨4,by rw[ot,C9 (by decide)];exact a⟩
  .exact⟨5,by rw[ot,C9 (by decide)];exact a⟩
  .exact⟨6,by rw[ot,C9 (by decide)];exact a⟩
  .exact⟨7,by rw[ot,C9 (by decide)];exact a⟩
  .exact⟨8,by rw[ot,C9 (by decide)];exact a⟩
  .exact⟨9,by rw[ot,C9 (by decide)];exact a⟩
def Kt (t u:Fq) (a:Fin 10) (q y:ℂ):Mt:=
 if a.val<4 then M4 t u (iz a) y else Q9 t u (iz a) (mr a) q y
def KO (a:Fin 10) (q y:ℂ): Prop :=if a.val<4 then y≠0 else (q≠0/\y≠0)
def Ut (t u:Fq) (f:t≠u) (c:Fin 10) (X:Mt) (h:ot t u c X):
  ∃ b q y:ℂ,b≠0/\KO c q y/\X=b•Kt t u c q y:=by
 by_cases a:c.val<4
 .simp only[ot,a,A9]at h;obtain⟨b,y,d,e,rfl⟩:=VC t u _ f X h
  exact⟨b,0,y,d,by simp[KO,a,e],by simp[Kt,a]⟩
 .simp only[ot,a,A8]at h
  obtain⟨b,q,y,d,g,e,rfl⟩:=Vy t u _ _ f (Qx c (by omega)) X h
  exact⟨b,q,y,d,by simp[KO,a,g,e],by simp[Kt,a]⟩
def Lq (g1 g2 g3:Mt): Prop :=
 (∀ a b c:ℂ,p4 (Bm+(a•g1+ b•g2+ c•g3))=65)/\
 (∀ a b c:ℂ,∀ d:Fq,m3 0 d (a•g1+ b•g2+ c•g3)=0)
def TN (h1 h2 h3:Mt) (k1 f g:ℂ) (i:k1≠0) (h:f≠0) (j:g≠0)
  (k:Lq (k1•h1) (f•h2) (g•h3)):Lq h1 h2 h3:=by
 obtain⟨l,m⟩:=k;have e:∀ a b c:ℂ,a•h1+ b•h2+ c•h3=
   (a/k1)•(k1•h1)+(b/f)•(f•h2)+(c/g)•(g•h3):=by
  intro a b c;simp only[H0,N0 _ i,N0 _ h,N0 _ j]
 refine⟨λa b c=> ?_,λa b c d=> ?_⟩
 .rw[e];exact l _ _ _
 .rw[e];exact m _ _ _ d
def LM (g1 g2 g3:Mt) (e:Lq g1 g2 g3):Lq g2 g1 g3:=by
 obtain⟨f,g⟩:=e
 refine⟨λa b c=> ?_,λa b c d=> ?_⟩
 .rw[show a•g2+ b•g1+ c•g3=b•g1+ a•g2+ c•g3 by abel];exact f _ _ _
 .rw[show a•g2+ b•g1+ c•g3=b•g1+ a•g2+ c•g3 by abel];exact g _ _ _ d
def M8 (g1 g2 g3:Mt) (e:Lq g1 g2 g3):Lq g1 g3 g2:=by
 obtain⟨f,g⟩:=e
 refine⟨λa b c=> ?_,λa b c d=> ?_⟩
 .rw[show a•g1+ b•g3+ c•g2=a•g1+ c•g2+ b•g3 by abel];exact f _ _ _
 .rw[show a•g1+ b•g3+ c•g2=a•g1+ c•g2+ b•g3 by abel];exact g _ _ _ d
def Rh (L:Sq) (g:∀ t∈L,p4 (Bm+ t)=65)
  (n:finrank ℂ (L.map (af 0))=3) (g1 e f:Mt) (k:g1∈Ar L 0) (l:e∈Ar L 0)
  (m:f∈Ar L 0):Lq g1 e f:=by
 have h:∀ a b c:ℂ,a•g1+ b•e+ c•f∈Ar L 0:=λa b c=>
  (Ar L 0).add_mem ((Ar L 0).add_mem ((Ar L 0).smul_mem a k) ((Ar L 0).smul_mem b l))
   ((Ar L 0).smul_mem c m)
 refine⟨λa b c=> g _ ((ei L 0 _).1 (h a b c)).1,λa b c d=> ?_⟩
 obtain⟨j,i⟩:=(ei L 0 _).1 (h a b c);exact VE L g 0 n _ j i d
def Vc (b c g3:Mt) (e:Lq b c g3):
  p4 (Bm+ b)=65/\p4 (Bm+ c)=65/\p4 (Bm+ g3)=65/\p4 (Bm+ b+ c)=65/\
  p4 (Bm+ b+ g3)=65/\p4 (Bm+ c+ g3)=65/\(∀ d,m3 0 d (b+ c+ g3)=0):=by
 obtain⟨a,f⟩:=e
 refine⟨?_,?_,?_,?_,?_,?_,λd=> ?_⟩
 .have :=a 1 0 0;simpa using this
 .have :=a 0 1 0;simpa using this
 .have :=a 0 0 1;simpa using this
 .have :=a 1 1 0;simpa[D1] using this
 .have :=a 1 0 1;simpa[D1] using this
 .have :=a 0 1 1;simpa[D1] using this
 .have :=f 1 1 1 d;simpa using this
def pt (k:Fin 6) (i:Fq):Fq:= ![![0,1,2,3],![0,2,1,3],![0,3,2,1],![0,1,3,2],![0,2,3,1],![0,3,1,2]] k i
def QU:∀ k:Fin 6,∀ i j:Fq,pt k i=pt k j->i=j:=by decide
def Nr (k:Fin 6) (X:Mt):Mt:=λq=> X (pt k q.1,pt k q.2)
lemma agl (k:Fin 6) (X:Mt):p4 (Bm+ Nr k X)=p4 (Bm+ X):=by
 fin_cases k<;>simp +decide [p4,Nr,pt,Bm]<;>ring
lemma agi (k:Fin 6) (d:Fq) (X:Mt):m3 0 d (Nr k X)=m3 0 (pt k d) X:=by
 fin_cases k<;>fin_cases d<;>simp +decide [m3,PV,Nr,pt]<;>ring
def LX (k:Fin 6) (g1 g2 g3:Mt) (hV:Lq g1 g2 g3):
  Lq (Nr k g1) (Nr k g2) (Nr k g3):=by
 obtain⟨f,g⟩:=hV;have e:∀ a b c:ℂ,a•Nr k g1+ b•Nr k g2+ c•Nr k g3=
   Nr k (a•g1+ b•g2+ c•g3):=by intro a b c;funext q;rfl
 refine⟨λa b c=> ?_,λa b c d=> ?_⟩
 .rw[e,agl];exact f a b c
 .rw[e,agi];exact g a b c _
def aaS (t u c:Fq) (X:Mt) (h:Mc t u c X):Mc u t c X:=by
 obtain⟨f,b,h2⟩:=h
 refine⟨λi j a=> f i j ?_,h2,b⟩
 rintro⟨d,e⟩;exact a ⟨d.symm,e⟩
def Yv (t u c d:Fq) (X:Mt) (h:Ke t u c d X):Ke u t c d X:=by
 obtain⟨hs,b,h2,h3,e,hp⟩:=h
 refine⟨λi j a=> hs i j ?_,h3,e,b,h2,by linear_combination hp⟩
 rintro⟨f,g⟩;exact a ⟨f.symm,g⟩
def Yu (t u c d:Fq) (X:Mt) (h:Ke t u c d X):Ke t u d c X:=by
 obtain⟨hs,b,h2,h3,e,hp⟩:=h
 refine⟨λi j a=> hs i j ?_,h2,b,e,h3,by linear_combination hp⟩
 rintro⟨f,g⟩;exact a ⟨f,g.symm⟩
def aaR (k:Fin 6) (t u c t' d a:Fq) (f:pt k t'=t) (g:pt k d=u)
  (b:pt k a=c) (X:Mt) (h:Mc t u c X):Mc t' d a (Nr k X):=by
 obtain⟨l,h1,h2⟩:=h
 refine⟨λi j e=> l (pt k i) (pt k j) ?_,?_,?_⟩
 .rintro⟨hi,hj⟩;apply e;refine⟨?_,QU k _ _ (hj.trans b.symm)⟩;rcases hi with hi | hi
  .exact Or.inl (QU k _ _ (hi.trans f.symm))
  .exact Or.inr (QU k _ _ (hi.trans g.symm))
 .show X (pt k t',pt k a)≠0
  rw[f,b];exact h1
 .show X (pt k d,pt k a)≠0
  rw[g,b];exact h2
def Vx (k:Fin 6) (t u c d t' u' a b:Fq) (g:pt k t'=t) (hu:pt k u'=u)
  (e:pt k a=c) (f:pt k b=d) (X:Mt) (h:Ke t u c d X):
  Ke t' u' a b (Nr k X):=by
 obtain⟨p,h1,l,m,n,o⟩:=h
 refine⟨λi j hij=> p (pt k i) (pt k j) ?_,?_,?_,?_,?_,?_⟩
 .rintro⟨hi,hj⟩;apply hij;constructor
  .rcases hi with hi | hi
   .exact Or.inl (QU k _ _ (hi.trans g.symm))
   .exact Or.inr (QU k _ _ (hi.trans hu.symm))
  .rcases hj with hj | hj
   .exact Or.inl (QU k _ _ (hj.trans e.symm))
   .exact Or.inr (QU k _ _ (hj.trans f.symm))
 .show X (pt k t',pt k a)≠0
  rw[g,e];exact h1
 .show X (pt k t',pt k b)≠0
  rw[g,f];exact l
 .show X (pt k u',pt k a)≠0
  rw[hu,e];exact m
 .show X (pt k u',pt k b)≠0
  rw[hu,f];exact n
 .show X (pt k t',pt k a)*X (pt k u',pt k b)+ X (pt k t',pt k b)*X (pt k u',pt k a)=0
  rw[g,hu,e,f];exact o
def K7 (t u:Fq) (a:Fin 10) (X:Mt) (h:ot t u a X):ot u t a X:=by
 by_cases b:a.val<4
 .simp only[ot,b,A9]at h ⊢;exact aaS _ _ _ X h
 .simp only[ot,b,A8]at h ⊢;exact Yv _ _ _ _ X h
def I5 (k:Fin 6) (a:Fin 10):Fin 10:= ![![0,1,2,3,4,5,6,7,8,9],![0,2,1,3,5,4,6,7,9,8],![0,3,2,1,6,5,4,9,8,7],![0,1,3,2,4,6,5,8,7,9],![0,3,1,2,6,4,5,8,9,7],![0,2,3,1,5,6,4,9,7,8]] k a
def ade:∀ k:Fin 6,∀ a:Fin 10,
    (a.val<4->(I5 k a).val<4/\pt k (iz (I5 k a))=iz a)/\
    (4≤ a.val->4≤(I5 k a).val/\
      ((pt k (iz (I5 k a))=iz a/\pt k (mr (I5 k a))=mr a)\/
       (pt k (iz (I5 k a))=mr a/\pt k (mr (I5 k a))=iz a))):=by decide
def oy (k:Fin 6) (b:Fin 10) (t u j l:Fq) (e:pt k j=t) (f:pt k l=u)
  (X:Mt) (h:ot t u b X):ot j l (I5 k b) (Nr k X):=by
 obtain⟨o,n⟩:=ade k b;by_cases c:b.val<4
 .obtain⟨g,a⟩:=o c;simp only[ot,c,g,A9]at h ⊢;exact aaR k _ _ _ _ _ _ e f a X h
 .obtain⟨g,m⟩:=n (by omega)
  have i:¬ (I5 k b).val<4:=by omega
  simp only[ot,c,i,A8]at h ⊢;rcases m with⟨a,d⟩ | ⟨a,d⟩
  .exact Vx k _ _ _ _ _ _ _ _ e f a d X h
  .exact Vx k _ _ _ _ _ _ _ _ e f a d X (Yu _ _ _ _ X h)
def ak (a b c:Fin 10): Prop :=
 ∀ g1 g2 d:Mt,ot 2 3 a g1->ot 1 3 b g2->ot 1 2 c d->Lq g1 g2 d->False
def Xw (a b c:Fin 10) (i:Fq):Fin 10:= ![a,a,b,c] i
def adi (a b c:Fin 10) (h:ak (I5 0 a) (I5 0 b) (I5 0 c)):ak a b c:=by
 intro e f g H1 H2 d hV
 exact h _ _ _ (oy 0 a 2 3 2 3 (by decide) (by decide) e H1)
  (oy 0 b 1 3 1 3 (by decide) (by decide) f H2)
  (oy 0 c 1 2 1 2 (by decide) (by decide) g d)
  (LX 0 _ _ _ hV)
def adk (a b c:Fin 10) (h:ak (I5 1 b) (I5 1 a) (I5 1 c)):ak a b c:=by
 intro e f g H1 H2 d hV
 exact h _ _ _ (oy 1 b 1 3 2 3 (by decide) (by decide) f H2)
  (oy 1 a 2 3 1 3 (by decide) (by decide) e H1)
  (oy 1 c 2 1 1 2 (by decide) (by decide) g (K7 _ _ _ _ d))
  (LM _ _ _ (LX 1 _ _ _ hV))
def adl (a b c:Fin 10) (h:ak (I5 2 c) (I5 2 b) (I5 2 a)):ak a b c:=by
 intro e f g H1 H2 d hV
 exact h _ _ _ (oy 2 c 2 1 2 3 (by decide) (by decide) g (K7 _ _ _ _ d))
  (oy 2 b 3 1 1 3 (by decide) (by decide) f (K7 _ _ _ _ H2))
  (oy 2 a 3 2 1 2 (by decide) (by decide) e (K7 _ _ _ _ H1))
  (LM _ _ _ (M8 _ _ _ (LM _ _ _ (LX 2 _ _ _ hV))))
def adn (a b c:Fin 10) (h:ak (I5 3 a) (I5 3 c) (I5 3 b)):ak a b c:=by
 intro e f g H1 H2 d hV
 exact h _ _ _ (oy 3 a 3 2 2 3 (by decide) (by decide) e (K7 _ _ _ _ H1))
  (oy 3 c 1 2 1 3 (by decide) (by decide) g d)
  (oy 3 b 1 3 1 2 (by decide) (by decide) f H2)
  (M8 _ _ _ (LX 3 _ _ _ hV))
def ado (a b c:Fin 10) (h:ak (I5 4 b) (I5 4 c) (I5 4 a)):ak a b c:=by
 intro e f g H1 H2 d hV
 exact h _ _ _ (oy 4 b 3 1 2 3 (by decide) (by decide) f (K7 _ _ _ _ H2))
  (oy 4 c 2 1 1 3 (by decide) (by decide) g (K7 _ _ _ _ d))
  (oy 4 a 2 3 1 2 (by decide) (by decide) e H1)
  (M8 _ _ _ (LM _ _ _ (LX 4 _ _ _ hV)))
def adp (a b c:Fin 10) (h:ak (I5 5 c) (I5 5 a) (I5 5 b)):ak a b c:=by
 intro e f g H1 H2 d hV
 exact h _ _ _ (oy 5 c 1 2 2 3 (by decide) (by decide) g d)
  (oy 5 a 3 2 1 3 (by decide) (by decide) e (K7 _ _ _ _ H1))
  (oy 5 b 3 1 1 2 (by decide) (by decide) f (K7 _ _ _ _ H2))
  (LM _ _ _ (M8 _ _ _ (LX 5 _ _ _ hV)))
def afT (k:Fin 6) (a b c:Fin 10)
  (h:ak (I5 k (Xw a b c (pt k 1))) (I5 k (Xw a b c (pt k 2))) (I5 k (Xw a b c (pt k 3)))):
  ak a b c:=by
 fin_cases k
 .exact adi a b c h
 .exact adk a b c h
 .exact adl a b c h
 .exact adn a b c h
 .exact ado a b c h
 .exact adp a b c h
def YK (a b c:Fin 10):Fin 6:=Fin.ofNat 6 (0x4f7c25b9d5382173a23125cc73cd12976f2dd14b346fa1e7415967c384e6e27d345745e844abbb2b40184b7a9452ba2e1b1dd9d102b713e1be8f0ff6cafb74816ca7e772996d2699855150e5815a9c7fe12ec31e99c76c23ab9a6690cd9acdbc23d2900a8f9a091c3d0c90b23e5392602b6cdc17b722e765527b229166eb71e5f476afdb6d8690b38cfcf1122cd91b5e1bf65a056be2a8ea3d1619ebb6104d4e0b8ea2dc65415652e781449c05a44629943ff1c34076f7e1a98906abafcf03611d591f6841591a931bb8b33db7b3d03bae0c3da08e265ddc4f5aa70010439fbd628fe0f694ebae0eaf717178f463bab17eade7420caedf9975283c54c54268bc437f5b571ebc2b05de7182cedfb2b298a1a0008e2d6fc25d1c15a007ff69a83a9ec79c0a9972a606fd58b9735f0a47a7bf6de4c893685428be0cf9c0b44f1699f61df4/6^(100*a.val+10*b.val+ c.val)%6)
def ciT (a b c:Fin 10):Fin 186:=Fin.ofNat 186 (0x83d0a59efa8d717f6f37219c59bed288729c96bedb39c0e080e17aa483cfdee5312284a29d39406abc3e88309e31b10f30f0aeadd95390df2e824f9cb3ee2cc00079ced0408bd3d5c617e80645aaa65f5485d5e0c7f807eab222f19b6a4567034a33efcc4dd0e9aa52b5418aca90e3b0e48e74173377978e455b9a6a779d2f4b3766e512a4d7ba6c76c7e48557bc3078f7fd1b643b01b6bbbaeb5a206688bd0d9e77d79ca3709dd0cdc257aba3d5fd1e0f3b5eec98a16dac6e42365f851b49c89e841094da58f9e177c745412e6af53526e1af42043993c8d771fab8a7fffea53f17892b55857251e7e2fcf00cb958a4b2f344ef9ff2b7e2a9da6a2d7cffceb771cf9b2f16a2a35e1d96892479893843bfb15afc1819a0d8fcde263849169d722f4f80ff7120680cddaa884b3dc294e54dc66651f2a2f6402e63db9f890c41af5ef6ba46c02645890212772a886c829d7dbadd123d2197ec88f0be39e3bf85099b34e4170074f464f398aeea9a4705c66f081b38b76061143914afc98a48dc720c33a843952513e78e7afc7f33a4036cd21abdd684e59557da524dfb7d4690b084b95879f7b65434c7d4f99aae4164cb811ee89bb05b2c79c8dc01a885b2b4146e31f241f5d14b91662858ec7a134c789fa3907cb8d7101542202b87b862c032175a0ea98dfb12bc4a6b8be69d215ea6eaac4fc19e8ff1b2d7eb014c74f3f07e6d0eeb73047c045aee8c6e3f62d6b2b476798dbb6d39212cde96b7c6157dc80018ca9e5115badc4ca9d2a272f49e5d3f05d98a4ea429da9724f327317d5728151b8a2444b966851a101cbc03dbd63c599462142ea666a918fbd82386aafeddda47db504537c2dca01ad22d0409dc7784a5635f9d4040ab67083636c287b9e0cc3f7ef587ff67750b49100ecd714feaba8fa0268ebca4d04be099ae5ce50d9aad96a0fdea09e2221cbc5909fd00dc44e26fec0a3f822d718e8ee416d1dffdd1cde062db69bf4b5c730eee643ef7e80f7756700b1eeae5fdc4f54ba143f39010a38a32c3ec744c8a247015a221ef02e1a8c24417b9e97e5728ec922d8e72897a1d8fff50f15840ccb34d63dbfc665d0283d2ef5e6a75ade55d904dd17a554172fb42a6090adb7af0fa7b67cb9cd5351439a1c74afa2513b9378e3ff7bf8b429df88038c460148a13ac1bf26674599dd54f4da684b49946c83d03119834e553076f966c6c2af95772263df38f4bfe2c933536cd503dcd580c7515ab4baa7802c566f13f8171c44de0c11e873e8b14b138a91c1c2fe5f66fbbc25b74efc3afe14a0c02802670eeb32e250ad2f4f53b0/186^(100*a.val+10*b.val+ c.val)%186)
def rA (i:Fin 186):Fin 10:=Fin.ofNat 10 (0x221111000000009999999999999977777777777777777777777777777777777777755555555555555555555555555555555555555555555555555555555555555555555444444444444444444444444444444444444444444444444444/16^i.val %16)
def rB (i:Fin 186):Fin 10:=Fin.ofNat 10 (0x313211322111003221110000888833333222222111111000000999998888888777733333332222222211111111000000009999999888888887777777766666666444444322111000099999888888777777766666666555555444444444/16^i.val %16)
def rC (i:Fin 186):Fin 10:=Fin.ofNat 10 (0x112332232321312323213210310732107321097321097321097321083210987310832109873210987532109875321098753210987321098753210987532109874310874232321321032109321097321098732109875310876321098765/16^i.val %16)
def ZJ:∀ a b c:Fin 10,¬ (a=b/\b=c)->
  I5 (YK a b c) (Xw a b c (pt (YK a b c) 1))=rA (ciT a b c)/\
  I5 (YK a b c) (Xw a b c (pt (YK a b c) 2))=rB (ciT a b c)/\
  I5 (YK a b c) (Xw a b c (pt (YK a b c) 3))=rC (ciT a b c):=by decide +kernel
def UN (d:∀ i:Fin 186,ak (rA i) (rB i) (rC i)) (a b c:Fin 10)
  (hna:¬ (a=b/\b=c)):ak a b c:=by
 apply afT (YK a b c);obtain⟨e,f,g⟩:=ZJ a b c hna;rw[e,f,g];exact d _
def VF (a b c:Mt): Prop :=
 p4 (Bm+ a)=65/\p4 (Bm+ b)=65/\p4 (Bm+ c)=65/\p4 (Bm+ a+ b)=65/\
 p4 (Bm+ a+ c)=65/\p4 (Bm+ b+ c)=65/\ ∀ d,m3 0 d (a+ b+ c)=0
def Yx (a b c:Fin 10)
  (h:∀ q1 e q2 f d g:ℂ,KO a q1 e->KO b q2 f->KO c d g->
   VF (Kt 2 3 a q1 e) (Kt 1 3 b q2 f) (Kt 1 2 c d g)->False):ak a b c:=by
 intro n o p H1 i j q
 obtain⟨u,q1,e,l,r,rfl⟩:=Ut 2 3 (by decide) a n H1
 obtain⟨v,q2,f,k,s,rfl⟩:=Ut 1 3 (by decide) b o i
 obtain⟨w,d,g,m,t,rfl⟩:=Ut 1 2 (by decide) c p j
 exact h q1 e q2 f d g r s t (Vc _ _ _ (TN _ _ _ _ _ _ l k m q))
def MU (i j:Fq):ℂ:=if i=j then 16 else 11
def aq (t u c d:Fq) (q:ℂ):Mt:=
 (q*MU u d- MU u c)•E t c+(q*(q*MU u d- MU u c))•E t d+(MU t c+ q*MU t d)•E u c
  +(-(q*(MU t c+ q*MU t d)))•E u d
def QH (a b c:Mt): Prop :=
 p4 (Bm+ a+ b)=65/\p4 (Bm+ a+ c)=65/\p4 (Bm+ b+ c)=65/\ ∀ d,m3 0 d (a+ b+ c)=0
def NV (X:Mt):ℂ:= ∑ i:Fq,∑ j:Fq,X (i,j)*MU i j
def QC (X:Mt) (h:∀ s:ℂ,p4 (Bm+ s•X)=65):NV X=0:=by
 have a:=h 1;have b:=h (-1);have c:=h 2;have d:=h (-2);simp +decide only[NV,MU,C2,p4,Bm,A1,A4,
  A5,A9,A8]at a b c d ⊢
 linear_combination (8*a-8*b- c+ d)/12
lemma ZU (X Y:Mt):NV (X+ Y)=NV X+ NV Y:=by
 simp only[NV,A1,add_mul,E8]
lemma R7 (a:ℂ) (X:Mt):NV (a•X)=a*NV X:=by
 simp only[NV,A4,A5,Finset.mul_sum,mul_assoc]
lemma aep (t c:Fq):NV (E t c)=MU t c:=by
 fin_cases t<;>fin_cases c<;>simp[NV,E,MU,C2]
def O9 (t u c d:Fq) (k:t≠u) (j:c≠d) (X:Mt) (h:Ke t u c d X)
  (l:NV X=0):∃ b q:ℂ,b≠0/\q≠0/\q*MU u d- MU u c≠0/\MU t c+ q*MU t d≠0/\
   X=b•aq t u c d q:=by
 obtain⟨b,q,y,i,m,n,rfl⟩:=Vy t u c d k j X h
 have o:MU t c+ q*MU t d+ y*MU u c+(-(q*y))*MU u d=0:=by
  have h0:=l;rw[R7]at h0
  have e:NV (Q9 t u c d q y)=MU t c+ q*MU t d+ y*MU u c+(-(q*y))*MU u d:=by
   simp only[Q9,ZU,R7,aep]
  rw[e]at h0;exact (A0.1 h0).resolve_left i
 have g:MU t c+ q*MU t d=y*(q*MU u d- MU u c):=by grind
 have f:q*MU u d- MU u c≠0:=by
  intro ha0
  have r:MU t c+ q*MU t d=0:=by rw[g,ha0,C3]
  have a:MU t c*MU u d+ MU u c*MU t d=0:=by grind
  simp only[MU]at a;split_ifs at a<;>norm_num at a
 refine⟨b/(q*MU u d- MU u c),q,L0 i f,m,f,?_,?_⟩
 .rw[g];exact mul_ne_zero n f
 .funext p;simp only[Q9,aq,A1,A4,A5];rw[g];field_simp
def fu (a b c:Fin 10) (G:4≤ a.val) (H:4≤ b.val) (J:4≤ c.val)
  (h:∀ q1 q2 d:ℂ,q1≠0->q1*MU 3 (mr a)- MU 3 (iz a)≠0->MU 2 (iz a)+ q1*MU 2 (mr a)≠0->
   q2≠0->q2*MU 3 (mr b)- MU 3 (iz b)≠0->MU 1 (iz b)+ q2*MU 1 (mr b)≠0->
   d≠0->d*MU 2 (mr c)- MU 2 (iz c)≠0->MU 1 (iz c)+ d*MU 1 (mr c)≠0->
   QH (aq 2 3 (iz a) (mr a) q1) (aq 1 3 (iz b) (mr b) q2) (aq 1 2 (iz c) (mr c) d)->False):
  ak a b c:=by
 intro f g g3 i j k e
 have l:¬ a.val<4:=by omega
 have p:¬ b.val<4:=by omega
 have r:¬ c.val<4:=by omega
 simp only[ot,l,p,r,A8]at i j k
 have D:NV f=0:=QC f (λs=> by simpa using e.1 s 0 0)
 have E:NV g=0:=QC g (λs=> by simpa using e.1 0 s 0)
 have F:NV g3=0:=QC g3 (λs=> by simpa using e.1 0 0 s)
 obtain⟨L,q1,z,hq1,m,B,rfl⟩:=O9 2 3 _ _ (by decide) (Qx a G) f i D
 obtain⟨M,q2,x,t,n,C,rfl⟩:=O9 1 3 _ _ (by decide) (Qx b H) g j E
 obtain⟨N,d,A,u,o,q,rfl⟩:=O9 1 2 _ _ (by decide) (Qx c J) g3 k F
 obtain⟨-,-,-,y,v,w,K⟩:=Vc _ _ _ (TN _ _ _ _ _ _ z x A e);exact h q1 q2 d hq1 m B t n C u o q ⟨y,v,w,K⟩
@[simp] lemma an7 (t u:Fq) (q y:ℂ):Kt t u 0 q y=M4 t u 0 y:=rfl
@[simp] lemma nz0 (q y:ℂ):KO 0 q y=(y≠0):=rfl
@[simp] lemma an8 (t u:Fq) (q y:ℂ):Kt t u 1 q y=M4 t u 1 y:=rfl
@[simp] lemma nz1 (q y:ℂ):KO 1 q y=(y≠0):=rfl
@[simp] lemma an9 (t u:Fq) (q y:ℂ):Kt t u 2 q y=M4 t u 2 y:=rfl
@[simp] lemma nz2 (q y:ℂ):KO 2 q y=(y≠0):=rfl
@[simp] lemma aoa (t u:Fq) (q y:ℂ):Kt t u 3 q y=M4 t u 3 y:=rfl
@[simp] lemma nz3 (q y:ℂ):KO 3 q y=(y≠0):=rfl
@[simp] lemma ahF (t u:Fq) (q y:ℂ):Kt t u 4 q y=Q9 t u 0 1 q y:=rfl
@[simp] lemma nz4 (q y:ℂ):KO 4 q y=(q≠0/\y≠0):=rfl
@[simp] lemma ahG (t u:Fq) (q y:ℂ):Kt t u 5 q y=Q9 t u 0 2 q y:=rfl
@[simp] lemma nz5 (q y:ℂ):KO 5 q y=(q≠0/\y≠0):=rfl
@[simp] lemma ahH (t u:Fq) (q y:ℂ):Kt t u 6 q y=Q9 t u 0 3 q y:=rfl
@[simp] lemma nz6 (q y:ℂ):KO 6 q y=(q≠0/\y≠0):=rfl
@[simp] lemma ahI (t u:Fq) (q y:ℂ):Kt t u 7 q y=Q9 t u 1 2 q y:=rfl
@[simp] lemma nz7 (q y:ℂ):KO 7 q y=(q≠0/\y≠0):=rfl
@[simp] lemma ahJ (t u:Fq) (q y:ℂ):Kt t u 8 q y=Q9 t u 1 3 q y:=rfl
@[simp] lemma nz8 (q y:ℂ):KO 8 q y=(q≠0/\y≠0):=rfl
@[simp] lemma ahK (t u:Fq) (q y:ℂ):Kt t u 9 q y=Q9 t u 2 3 q y:=rfl
@[simp] lemma nz9 (q y:ℂ):KO 9 q y=(q≠0/\y≠0):=rfl
def SH (a b c:Fin 10)
  (h:∀ q1 f d g e y3:ℂ,KO a q1 f->KO b d g->KO c e y3->
   p4 (Bm+ Kt 2 3 a q1 f)=65->p4 (Bm+ Kt 1 3 b d g)=65->p4 (Bm+ Kt 1 2 c e y3)=65->
   p4 (Bm+ Kt 2 3 a q1 f+ Kt 1 3 b d g)=65->p4 (Bm+ Kt 2 3 a q1 f+ Kt 1 2 c e y3)=65->p4 (Bm+ Kt 1 3 b d g+ Kt 1 2 c e y3)=65->
   m3 0 0 (Kt 2 3 a q1 f+ Kt 1 3 b d g+ Kt 1 2 c e y3)=0->m3 0 1 (Kt 2 3 a q1 f+ Kt 1 3 b d g+ Kt 1 2 c e y3)=0->m3 0 2 (Kt 2 3 a q1 f+ Kt 1 3 b d g+ Kt 1 2 c e y3)=0->m3 0 3 (Kt 2 3 a q1 f+ Kt 1 3 b d g+ Kt 1 2 c e y3)=0->False):ak a b c:=
 Yx a b c λq1 f d g e y3 i j k hF=>
  h q1 f d g e y3 i j k hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hF.2.2.2.2.1 hF.2.2.2.2.2.1
   (hF.2.2.2.2.2.2 0) (hF.2.2.2.2.2.2 1) (hF.2.2.2.2.2.2 2) (hF.2.2.2.2.2.2 3)
def VG {R: Type} (f:R->R->R):List R->List R->List R
 | [],b=> b
 | a::as,[]=> a::as
 | a::as,b::bs=> f a b::VG f as bs
def YA {R: Type} (z:R) (f g:R->R->R):List R->List R->List R
 | [],_=>[]
 | a::as,b=> VG f (b.map (g a)) (z::YA z f g as b)
def Z4 {R: Type} (t:R->Bool):List R->Bool
 | []=> true
 | a::as=> t a && Z4 t as
def ld {R: Type} (e:R->ℂ) (x:ℂ):List R->ℂ
 | []=>0
 | a::as=> e a+ x*ld e x as
lemma TJ {R: Type} (e:R->ℂ) (f:R->R->R) (c:∀ a b,e (f a b)=e a+ e b) (x:ℂ):
  ∀ p q:List R,ld e x (VG f p q)=ld e x p+ ld e x q
 | [],q=> by simp[VG,ld]
 | a::as,[]=> by simp[VG,ld]
 | a::as,b::bs=> by
  simp only[VG,ld,c,TJ e f c x as bs];ring
lemma Z3 {R: Type} (e:R->ℂ) (g:R->R->R) (c:∀ a b,e (g a b)=e a*e b) (x:ℂ) (a:R):
  ∀ q:List R,ld e x (q.map (g a))=e a*ld e x q
 | []=> by simp[ld]
 | b::bs=> by
  simp only[L1,ld,c,Z3 e g c x a bs];ring
lemma VH {R: Type} (e:R->ℂ) (z:R) (f g:R->R->R) (hz:e z=0)
  (c:∀ a b,e (f a b)=e a+ e b) (d:∀ a b,e (g a b)=e a*e b) (x:ℂ):
  ∀ p q:List R,ld e x (YA z f g p q)=ld e x p*ld e x q
 | [],q=> by simp[YA,ld]
 | a::as,q=> by
  simp only[YA,TJ e f c,Z3 e g d,ld,hz,VH e z f g hz c d x as q];ring
lemma VI {R: Type} (e:R->ℂ) (t:R->Bool) (b:∀ a,t a=true ->e a=0) (x:ℂ):
  ∀ p:List R,Z4 t p=true ->ld e x p=0
 | [],_=> by simp[ld]
 | a::as,h=> by
  simp only[Z4,D8]at h;simp only[ld,b a h.1,VI e t b x as h.2];ring
abbrev P1:=List ℤ
abbrev P2:=List P1
abbrev P3:=List P2
def Ry:P1->P1->P1:=VG (λa b=> a+ b)
def oz:P1->P1->P1:=YA 0 (λa b=> a+ b) (λa b=> a*b)
def Lo:P2->P2->P2:=VG Ry
def Il:P2->P2->P2:=YA [] Ry oz
def Mj:P3->P3->P3:=VG Lo
def Iu:P3->P3->P3:=YA [] Lo Il
def Rz1:P1->Bool:=Z4 (λc=> c==0)
def Rz2:P2->Bool:=Z4 Rz1
def Rz3:P3->Bool:=Z4 Rz2
def gn (x:ℂ):P1->ℂ:=ld (λc:ℤ=>(c:ℂ)) x
def ly (x y:ℂ):P2->ℂ:=ld (gn x) y
def ew (x y z:ℂ):P3->ℂ:=ld (ly x y) z
def Sb (x:ℂ) (p q:P1):gn x (Ry p q)=gn x p+ gn x q:=by
 unfold gn Ry
 exact TJ _ _ (λa b=> by simp only[Int.cast_add]) x p q
lemma Lj (x:ℂ) (p q:P1):gn x (oz p q)=gn x p*gn x q:=by
 unfold gn oz
 exact VH _ _ _ _ (by simp only[N2]) (λa b=> by simp only[Int.cast_add])
  (λa b=> by simp only[Int.cast_mul]) x p q
def aaY (x:ℂ) (p:P1) (h:Rz1 p=true):gn x p=0:=by
 unfold gn
 exact VI _ _ (λc a=> by simp only[beq_iff_eq]at a;simp only[a,N2]) x p h
def aaZ (x y:ℂ) (p q:P2):ly x y (Lo p q)=ly x y p+ ly x y q:=by
 unfold ly Lo
 exact TJ _ _ (λa b=> Sb x a b) y p q
def aes (x y:ℂ) (p q:P2):ly x y (Il p q)=ly x y p*ly x y q:=by
 unfold ly Il
 exact VH _ _ _ _ (by simp only[gn,ld]) (λa b=> Sb x a b) (λa b=> Lj x a b) y p q
def aj7 (x y:ℂ) (p:P2) (h:Rz2 p=true):ly x y p=0:=by
 unfold ly
 exact VI _ _ (λa ha=> aaY x a ha) y p h
lemma Q8 (x y z:ℂ) (p q:P3):ew x y z (Mj p q)=ew x y z p+ ew x y z q:=by
 unfold ew Mj
 exact TJ _ _ (λa b=> aaZ x y a b) z p q
lemma Np (x y z:ℂ) (p q:P3):ew x y z (Iu p q)=ew x y z p*ew x y z q:=by
 unfold ew Iu
 exact VH _ _ _ _ (by simp only[ly,ld]) (λa b=> aaZ x y a b) (λa b=> aes x y a b) z p q
def aeu (x y z:ℂ) (p:P3) (h:Rz3 p=true):ew x y z p=0:=by
 unfold ew
 exact VI _ _ (λa ha=> aj7 x y a ha) z p h
def Rsp:List (P3× P3)->P3
 | []=>[]
 | (a,b)::l=> Mj (Iu a b) (Rsp l)
def aaX (L:List (P3× P3)):Bool:=Rz3 (Rsp L)
lemma ab6 (x y z:ℂ):∀ L:List (P3× P3),
  ew x y z (Rsp L)=(L.map (λp=> ew x y z p.1*ew x y z p.2)).sum
 | []=> by simp[Rsp,ew,ld]
 | (a,b)::l=> by
  simp only[Rsp,Q8,Np,ab6 x y z l,L1,N3]
def rz (L:List (P3× P3)) (h:aaX L=true) (x y z:ℂ):
  (L.map (λp=> ew x y z p.1*ew x y z p.2)).sum=0:=by
 rw[<- ab6];exact aeu x y z _ h
def Rn1 (p:P1):P1:=p.map (λc=> -c)
def Rs1 (p q:P1):P1:=Ry p (Rn1 q)
def Rn2 (p:P2):P2:=p.map Rn1
def VJ (p q:P2):P2:=Lo p (Rn2 q)
def Rc2 (c:P1) (p:P2):P2:=p.map (oz c)
def Rsh {a: Type} (z:a):Nat->List a->List a
 | 0,p=> p
 | n+1,p=> z::Rsh z n p
def Sc (p:P3):Nat->P3
 | 0=>[[[1]]]
 | n+1=> Iu p (Sc p n)
def Nq (p:P1):Nat->P1
 | 0=>[1]
 | n+1=> oz p (Nq p n)
def agQ (a b:Int):Int->List Int->List Int
 | _,[]=>[]
 | g,x::xs=> match (x- a*g)/b with
  | g'=> g'::agQ a b g' xs
def anl (a b:Int) (p:P1):P1:=(agQ a b 0 (p.drop 1).reverse).reverse
def agR (a b:Int):P1->List P1->List P1
 | _,[]=>[]
 | g,x::xs=> match (Rs1 x (g.map (λc=> a*c))).map (λc=> c/b) with
  | g'=> g'::agR a b g' xs
def anm (v:Nat) (a b:Int) (p:P2):P2:=
 if v=0 then p.map (anl a b) else (agR a b [] (p.drop 1).reverse).reverse
def aa0 (v:Nat) (a b:Int):P3:=if v=0 then [[[a,b]]] else [[[a],[b]]]
def M6:List (Nat× Int× Int)->P3
 | []=>[[[1]]]
 | t::l=> Iu (aa0 t.1 t.2.1 t.2.2) (M6 l)
def ads (p:P2):List (Nat× Int× Int)->P2
 | []=> p
 | t::l=> ads (anm t.1 t.2.1 t.2.2 p) l
def NX (p:P3) (i:Nat):P2:=p.getD i []
def ZW (F B:P3):P3× P3× P2:=
  match NX F 0,NX F 1,NX F 2,NX B 0,NX B 1,NX B 2 with
  | F0,F1,F2,B0,B1,B2=>
    if F.length≤2 then
      ([Rn2 (VJ (Il F1 B1) (Il F0 B2)),Rn2 (Il F1 B2)],[Il F1 F1],
       Lo (VJ (Il (Il F1 F1) B0) (Il (Il F0 F1) B1)) (Il (Il F0 F0) B2))
    else
    match VJ (Il F2 B0) (Il F0 B2),VJ (Il F2 B1) (Il F1 B2),VJ (Il F1 B0) (Il F0 B1) with
    | a,d21,d10=>
      ([VJ (Il d21 B1) (Il a B2),Il d21 B2],[VJ (Il a F2) (Il d21 F1),Rn2 (Il d21 F2)],
       VJ (Il a a) (Il d21 d10))
def Rpd (P:P2) (a:P1) (dg:Nat):Nat->P2->P2->Nat->P2× P2× Nat
 | 0,C,Q,k=>(Q,C,k)
 | n+1,C,Q,k=>
  if C.length≤ dg then (Q,C,k) else
  match C.getLastD [] with
  | lc=> Rpd P a dg n ((VJ (Rc2 a C) (Rsh [] (C.length-1- dg) (Rc2 lc P))).dropLast)
       (Lo (Rc2 a Q) (Rsh [] (C.length-1- dg) [lc])) (k+1)
def Qn (n:Int) (d:Nat):Int× Nat:=
 match Nat.gcd n.natAbs d with
 | g=>(n/(g:Int),d/g)
def ani (a b:Int× Nat):Int× Nat:=Qn (a.1*b.2+ b.1*a.2) (a.2*b.2)
def ank (a b:Int× Nat):Int× Nat:=Qn (a.1*b.1) (a.2*b.2)
def anj (a b:Int× Nat):Int× Nat:=
 if b.1<0 then Qn (-(a.1*b.2)) (a.2*b.1.natAbs) else Qn (a.1*b.2) (a.2*b.1.natAbs)
abbrev QP:=List (Int× Nat)
def Qtr (p:QP):QP:=(p.reverse.dropWhile (λc=> c.1==0)).reverse
def Qpa:QP->QP->QP
 | [],b=> b
 | a::as,[]=> a::as
 | a::as,b::bs=> ani a b::Qpa as bs
def Qsc (c:Int× Nat) (p:QP):QP:=p.map (ank c)
def Qpm:QP->QP->QP
 | [],_=>[]
 | a::as,b=> Qpa (Qsc a b) ((0,1)::Qpm as b)
def Qps (a b:QP):QP:=Qtr (Qpa a (Qsc (-1,1) b))
def Qdm (b:QP):Nat->QP->QP->QP× QP
 | 0,a,q=>(q,a)
 | n+1,a,q=>
  if a.length< b.length then (q,a) else
  match anj (a.getLastD (0,1)) (b.getLastD (0,1)),a.length- b.length with
  | t,s=> Qdm b n (Qtr (Qps a (Rsh (0,1) s (Qsc t b)))) (Qpa q (Rsh (0,1) s [t]))
def Qxg:Nat->QP->QP->QP->QP->QP->QP->QP× QP× QP
 | 0,r0,s0,t0,_,_,_=>(r0,s0,t0)
 | n+1,r0,s0,t0,r1,s1,t1=>
  if r1.isEmpty then (r0,s0,t0) else
  match Qdm r1 (r0.length+1) r0 [] with
  | (q,r)=> Qxg n r1 s1 t1 r (Qps s0 (Qpm q s1)) (Qps t0 (Qpm q t1))
def ofZ (p:P1):QP:=Qtr (p.map (λc=>(c,1)))
def aaW (p:QP):Nat:=p.foldl (λa c=> Nat.lcm a c.2) 1
def toZ (L:Nat) (p:QP):P1:=p.map (λc=> c.1*((L/c.2:Nat):Int))
def YE (a b:P1):P1× P1× P1:=
 match Qxg (a.length+ b.length+2) (ofZ a) [(1,1)] [] (ofZ b) [] [(1,1)] with
 | (g,s,t)=> match Nat.lcm (aaW g) (Nat.lcm (aaW s) (aaW t)) with
  | L=>(toZ L s,toZ L t,toZ L g)
def Zqt (a G:P1):P1× Nat:=
 match Qdm (ofZ G) (a.length+1) (ofZ a) [] with
 | (h,_)=> match aaW h with
  | c=>(toZ c h,c)
def lx (p:P1):P3:=[[p]]
def Kz (p:P2):P3:=[p]
structure FBC where
 u13:P3
 w13:P3
 k13:P2
 u23:P3
 w23:P3
 k23:P2
 aK13:P3
 Q13:P2
 R13:P2
 aK23:P3
 Q23:P2
 R23:P2
 E1:P1
 E2:P1
 E3:P1
 W:P2
 W3:P2
 S1:P1
 S2:P1
 S3:P1
 G6:P1
 H6:P1
 c6:Nat
 bK:P3
 Q1:P2
 F1:P2
 S7:P1
 T7:P1
 G7:P1
 H7:P1
 c7:Nat
def YS (F Sz k P:P3) (i j:List (Nat× Int× Int)) (e:P1) (m:Nat):FBC:=
 match ZW F Sz,ZW F k,NX P 0 with
 | (u13,w13,f),(u23,w23,res23),P2=>
  match ads f i,ads res23 j,P2.getD 0 [],P2.getD 1 [],P2.getD 2 [] with
  | k13,k23,c,b,a=>
   match Rpd P2 a 2 (k13.length+1) k13 [] 0,Rpd P2 a 2 (k23.length+1) k23 [] 0 with
   | (Q13,R13,g),(Q23,R23,n23)=>
    match R13.getD 0 [],R13.getD 1 [],R23.getD 0 [],R23.getD 1 [] with
    | r0,r1,s0,s1=>
     match Rs1 (oz s1 r0) (oz r1 s0),Ry (Rs1 (oz a (oz r0 r0)) (oz b (oz r0 r1))) (oz c (oz r1 r1)),
        Ry (Rs1 (oz a (oz s0 s0)) (oz b (oz s0 s1))) (oz c (oz s1 s1)) with
     | E1,E2,E3=>
      match YE E1 E2,Rpd [c,b] b 1 (k13.length+1) k13 [] 0 with
      | (l,n,h),(Q1,F1,nb)=>
       match YE h E3,YE a (F1.getD 0 []) with
       | (d,o,G6),(S7,T7,G7)=>
        match Zqt (oz e (Nq a m)) G6,Zqt e G7 with
        | (H6,c6),(H7,c7)=>
         { u13:=u13,w13:=w13,k13:=k13,u23:=u23,w23:=w23,k23:=k23,
           aK13:=Sc (lx a) g,Q13:=Q13,R13:=R13,aK23:=Sc (lx a) n23,Q23:=Q23,R23:=R23,
           E1:=E1,E2:=E2,E3:=E3,W:=[Ry (Rn1 (oz a r0)) (oz b r1),oz a r1],
           W3:=[Ry (Rn1 (oz a s0)) (oz b s1),oz a s1],
           S1:=oz d l,S2:=oz d n,S3:=o,G6:=G6,H6:=H6,c6:=c6,
           bK:=Sc (lx b) nb,Q1:=Q1,F1:=F1,S7:=S7,T7:=T7,G7:=G7,H7:=H7,c7:=c7 }
def ZV:P3:=[[[1]]]
def Mb:P3:=[[[-1]]]
def aj3:P3:=[[[],[],[-1]]]
def aai (c:FBC) (F f e P:P3) (b d:P3) (a:P1) (m:Nat):List (List (P3× P3)):=
 [ [(c.u13,F),(c.w13,f),(Iu Mb b,Kz c.k13)],
  [(c.u23,F),(c.w23,e),(Iu Mb d,Kz c.k23)],
  [(c.aK13,Kz c.k13),(Iu Mb (Kz c.Q13),P),(Mb,Kz c.R13)],
  [(c.aK23,Kz c.k23),(Iu Mb (Kz c.Q23),P),(Mb,Kz c.R23)],
  [(ZV,lx c.E1),(Iu Mb (lx (c.R23.getD 1 [])),Kz c.R13),(lx (c.R13.getD 1 []),Kz c.R23)],
  [(ZV,lx c.E2),(Iu Mb (lx (oz (c.R13.getD 1 []) (c.R13.getD 1 []))),P),(Kz c.R13,Kz c.W)],
  [(ZV,lx c.E3),(Iu Mb (lx (oz (c.R23.getD 1 []) (c.R23.getD 1 []))),P),(Kz c.R23,Kz c.W3)],
  [(lx c.S1,lx c.E1),(lx c.S2,lx c.E2),(lx c.S3,lx c.E3),(Mb,lx c.G6)],
  [(lx c.G6,lx c.H6),(Iu [[[-(c.c6:Int)]]] (Sc (lx ((NX P 0).getD 2 [])) m),lx a)],
  [(ZV,P),(aj3,lx ((NX P 0).getD 2 [])),(Mb,[[(NX P 0).getD 0 [],(NX P 0).getD 1 []]])],
  [(c.bK,Kz c.k13),(Iu Mb (Kz c.Q1),[[(NX P 0).getD 0 [],(NX P 0).getD 1 []]]),(Mb,Kz c.F1)],
  [(lx c.S7,lx ((NX P 0).getD 2 [])),(lx c.T7,Kz c.F1),(Mb,lx c.G7)],
  [(lx c.G7,lx c.H7),([[[-(c.c7:Int)]]],lx a)] ]
def YT (c:FBC) (F d QZ P:P3) (a b:List (Nat× Int× Int)) (e:P1) (m:Nat):Bool:=
 (aai c F d QZ P (M6 a) (M6 b) e m).all aaX && (c.c6 !=0) && (c.c7 !=0)
def UD (F d c P:P3) (a b:List (Nat× Int× Int)) (e:P1) (m:Nat):Bool:=
 YT (YS F d c P a b e m) F d c P a b e m
lemma aet (x y z:ℂ) (k:ℤ):ew x y z [[[k]]]=(k:ℂ):=by
 simp[ew,ly,gn,ld]
lemma af1 (x y z:ℂ):ew x y z ZV=1:=by simp[ZV,ew,ly,gn,ld]
lemma Yz (x y z:ℂ):ew x y z Mb= -1:=by simp[Mb,ew,ly,gn,ld]
lemma ZY (x y z:ℂ) (p:P3):∀ n:Nat,ew x y z (Sc p n)=(ew x y z p)^n
 | 0=> by
  show ew x y z [[[1]]]=_
  simp[ew,ly,gn,ld]
 | n+1=> by
  show ew x y z (Iu p (Sc p n))=_
  rw[Np,ZY x y z p n,pow_succ];ring
def XJ (F n QZ P:P3) (d e:List (Nat× Int× Int)) (a:P1) (m:Nat)
  (g:UD F n QZ P d e a m=true) (x y z:ℂ)
  (Q:ew x y z F=0) (Z:ew x y z n=0) (o9:ew x y z QZ=0) (b:ew x y z P=0)
  (B:ew x y z (M6 d)≠0) (C:ew x y z (M6 e)≠0)
  (R:ew x y z (lx a)≠0):False:=by
 unfold UD at g;generalize YS F n QZ P d e a m=c at g;rcases c with⟨u13,w13,k13,u23,w23,k23,aK13,Q13,R13,aK23,Q23,R23,E1,E2,E3,W,W3,S1,S2,S3,
  G6,H6,c6,bK,Q1,F1,S7,T7,G7,H7,c7⟩
 simp only[YT,aai,List.all_cons,List.all_nil,Bool.and_true,D8]at g;obtain⟨⟨⟨i1,i2,i3,i4,i5,i6,i7,i8,i9,U,V,X,Y⟩,S⟩,T⟩:=g;have e1:=rz _ i1 x y z;have G:=rz _ i2 x y z;have H:=rz _ i3 x y z;have J:=rz _ i4 x y z;have K:=rz _ i5 x y z;have L:=rz _ i6 x y z;have M:=rz _ i7 x y z;have N:=rz _ i8 x y z;have O:=rz _ i9 x y z;have k:=rz _ U x y z;have l:=rz _ V x y z;have v:=rz _ X x y z;have w:=rz _ Y x y z;simp only[L1,List.map_nil,N3,List.sum_nil,B8,Np,Yz,af1,
  ZY,aet]at e1 G H J K L M N O k l v w
 have E:c6≠0:=by simpa using S
 have A:c7≠0:=by simpa using T
 rw[Q,Z]at e1;rw[Q,o9]at G
 have j:ew x y z (Kz k13)=0:=by
  have h:ew x y z (M6 d)*ew x y z (Kz k13)=0:=by grind
  exact (A0.1 h).resolve_left B
 have D:ew x y z (Kz k23)=0:=by
  have h:ew x y z (M6 e)*ew x y z (Kz k23)=0:=by grind
  exact (A0.1 h).resolve_left C
 rw[j,b]at H;rw[D,b]at J
 have agN:ew x y z (Kz R13)=0:=by grind
 have i:ew x y z (Kz R23)=0:=by grind
 rw[agN,i]at K;rw[b,agN]at L;rw[b,i]at M
 have p:ew x y z (lx E1)=0:=by grind
 have q:ew x y z (lx E2)=0:=by grind
 have r:ew x y z (lx E3)=0:=by grind
 rw[p,q,r]at N
 have t:ew x y z (lx G6)=0:=by grind
 rw[t]at O;by_cases o:ew x y z (lx ((NX P 0).getD 2 []))=0
 .rw[b,o]at k
  have Lz:ew x y z [[(NX P 0).getD 0 [],(NX P 0).getD 1 []]]=0:=by grind
  rw[j,Lz]at l
  have s:ew x y z (Kz F1)=0:=by grind
  rw[o,s]at v
  have u:ew x y z (lx G7)=0:=by grind
  rw[u]at w
  have h:((-(c7:ℤ):ℤ):ℂ)*ew x y z (lx a)=0:=by grind
  rcases A0.1 h with h' | h'
  .push_cast at h'
   exact A (by exact_mod_cast D4.1 h')
  .exact R h'
 .have h:((-(c6:ℤ):ℤ):ℂ)*(ew x y z (lx ((NX P 0).getD 2 [])))^m*ew x y z (lx a)=0:=by
   grind
  rcases A0.1 h with h' | h'
  .rcases A0.1 h' with f | f
   .push_cast at f
    exact E (by exact_mod_cast D4.1 f)
   .exact N4 m o f
  .exact R h'
def Cs (k:ℤ):P3:=[[[k]]]
def Vq (v:Nat):P3:=if v=0 then [[[0,1]]] else if v=1 then [[[],[1]]] else [[],[[1]]]
abbrev MS:=Fq× Fq->P3
def o5 (i j:Fq):ℤ:=if i=j then 16 else 11
def ES (i j:Fq):MS:=λp=> if p.1=i/\p.2=j then Cs 1 else []
def QI (M N:MS):MS:=λp=> Mj (M p) (N p)
def smS (a:P3) (M:MS):MS:=λp=> Iu a (M p)
def Qi (t u c d:Fq) (v:P3):MS:=
 QI (QI (QI (smS (Mj (Iu v (Cs (o5 u d))) (Cs (-o5 u c))) (ES t c))
  (smS (Iu v (Mj (Iu v (Cs (o5 u d))) (Cs (-o5 u c)))) (ES t d)))
  (smS (Mj (Cs (o5 t c)) (Iu v (Cs (o5 t d)))) (ES u c)))
  (smS (Iu (Cs (-1)) (Iu v (Mj (Cs (o5 t c)) (Iu v (Cs (o5 t d)))))) (ES u d))
def BmS:MS:=λp=> if p.1=p.2 then Cs 2 else Cs 1
def ZC (a b c d e g h k:P3):P3:=Iu (Mj (Iu a b) (Iu c d)) (Mj (Iu e g) (Iu h k))
def p4S (M:MS):P3:=
 Mj (ZC (M (0,0)) (M (1,1)) (M (0,1)) (M (1,0)) (M (2,2)) (M (3,3)) (M (2,3)) (M (3,2)))
 (Mj (ZC (M (0,0)) (M (1,2)) (M (0,2)) (M (1,0)) (M (2,1)) (M (3,3)) (M (2,3)) (M (3,1)))
 (Mj (ZC (M (0,0)) (M (1,3)) (M (0,3)) (M (1,0)) (M (2,1)) (M (3,2)) (M (2,2)) (M (3,1)))
 (Mj (ZC (M (0,1)) (M (1,2)) (M (0,2)) (M (1,1)) (M (2,0)) (M (3,3)) (M (2,3)) (M (3,0)))
 (Mj (ZC (M (0,1)) (M (1,3)) (M (0,3)) (M (1,1)) (M (2,0)) (M (3,2)) (M (2,2)) (M (3,0)))
 (ZC (M (0,2)) (M (1,3)) (M (0,3)) (M (1,2)) (M (2,0)) (M (3,1)) (M (2,1)) (M (3,0)))))))
def p3S (g a e h i f b c d:P3):P3:=
 Mj (Iu (Iu g i) d) (Mj (Iu (Iu g f) c) (Mj (Iu (Iu a h) d)
 (Mj (Iu (Iu a f) b) (Mj (Iu (Iu e h) c) (Iu (Iu e i) b)))))
def m3S (r c:Fq) (X:MS):P3:=
 p3S (X (r+1,c+1)) (X (r+1,c+2)) (X (r+1,c+3)) (X (r+2,c+1)) (X (r+2,c+2)) (X (r+2,c+3))
  (X (r+3,c+1)) (X (r+3,c+2)) (X (r+3,c+3))
def PS (B1 B2:MS):P3:=Mj (p4S (QI (QI BmS B1) B2)) (Cs (-65))
def tr1 (p:P1):P1:=(p.reverse.dropWhile (· ==0)).reverse
def tr2 (p:P2):P2:=((p.map tr1).reverse.dropWhile List.isEmpty).reverse
def R2 (p:P3):P3:=((p.map tr2).reverse.dropWhile List.isEmpty).reverse
def XE (a b:P3):Bool:=Rz3 (Mj a (Iu (Cs (-1)) b))
def SB (a:Fin 10):MS:=Qi 2 3 (iz a) (mr a) (Vq 0)
def SE (b:Fin 10):MS:=Qi 1 3 (iz b) (mr b) (Vq 1)
def SF (c:Fin 10):MS:=Qi 1 2 (iz c) (mr c) (Vq 2)
def aef (e:Nat):P3:=if e=0 then Cs 1 else Vq (e-1)
def aee (w:Nat):P3:=
 if w=0 then Cs 1 else if w=1 then [[[0,1],[-1]]] else if w=2 then [[[],[1]],[[-1]]] else [[[0,1]],[[1]]]
def abm (w:Nat) (x y z:ℂ):ℂ:=if w=0 then 1 else if w=1 then x- y else if w=2 then y- z else x+ z
def pr (a b A B:ℤ):Bool:=a*B==b*A
def nzK (a b:Fin 10) (t:Nat× ℤ× ℤ):Bool:=
 (t.2.1 !=0 || t.2.2 !=0) && (t.2.1==0 || (t.1==0 && (pr t.2.1 t.2.2 (-o5 3 (iz a)) (o5 3 (mr a)) ||
  pr t.2.1 t.2.2 (o5 2 (iz a)) (o5 2 (mr a)))) || (t.1 !=0 && (pr t.2.1 t.2.2 (-o5 3 (iz b)) (o5 3 (mr b)) ||
  pr t.2.1 t.2.2 (o5 1 (iz b)) (o5 1 (mr b)))))
def TtS (a:Fin 10):P1:=Nq (oz (oz [0,1] [-o5 3 (iz a),o5 3 (mr a)]) [o5 2 (iz a),o5 2 (mr a)]) 4
def fBc (a b c:Fin 10) (d:Fq) (k:ℤ) (e w:Nat) (F:P3) (Km Ky:List (Nat× ℤ× ℤ)):Bool:=
 XE (m3S 0 d (QI (QI (SB a) (SE b)) (SF c))) (Iu (Iu (Iu (Cs k) (aef e)) (aee w)) F) && k !=0 &&
 e≤3 && XE (R2 (PS (SB a) (SF c))) (PS (SB a) (SF c)) && XE (R2 (PS (SE b) (SF c))) (PS (SE b) (SF c)) &&
 XE (R2 (PS (SB a) (SE b))) (PS (SB a) (SE b)) && Km.all (nzK a b) && Ky.all (nzK a b) &&
 UD F (R2 (PS (SB a) (SF c))) (R2 (PS (SE b) (SF c))) (R2 (PS (SB a) (SE b))) Km Ky (TtS a) 3
lemma QG (x y z:ℂ) (k:ℤ):ew x y z (Cs k)=k:=aet x y z k
lemma ZX (x y z:ℂ):ew x y z []=0:=rfl
lemma Rz (x:ℂ) (p:P1):∀ n:Nat,gn x (Nq p n)=(gn x p)^n
 | 0=> by simp[Nq,gn,ld]
 | n+1=> by rw[Nq,Lj,Rz x p n,pow_succ];ring
lemma LD (a b:P3) (h:XE a b=true) (x y z:ℂ):ew x y z a=ew x y z b:=by
 have h0:=aeu x y z (Mj a (Iu (Cs (-1)) b)) h;rw[Q8,Np,QG]at h0;push_cast at h0;grind
lemma Va (i j:Fq):MU i j=((o5 i j:ℤ):ℂ):=by
 unfold MU o5;split_ifs<;>norm_num
lemma amZ (x y z:ℂ) (i j:Fq) (p:Fq× Fq):ew x y z (ES i j p)=E i j p:=by
 unfold ES E;split_ifs<;>simp[QG,ZX]
lemma abS (x y z:ℂ) (t u c d:Fq) (v:P3) (p:Fq× Fq):
  ew x y z (Qi t u c d v p)=aq t u c d (ew x y z v) p:=by
 simp only[Qi,QI,smS,Q8,Np,QG,amZ,aq,A1,A4,A5,Va];push_cast;ring
lemma ajF (x y z:ℂ) (p:Fq× Fq):ew x y z (BmS p)=Bm p:=by
 unfold BmS Bm;split_ifs<;>simp[QG]
def Ev (x y z:ℂ) (M:MS):Mt:=λp=> ew x y z (M p)
lemma aju (x y z:ℂ) (M:MS):ew x y z (p4S M)=p4 (Ev x y z M):=by
 simp only[p4S,ZC,p4,Ev,Q8,Np];ring
lemma ajf (x y z:ℂ) (r c:Fq) (M:MS):ew x y z (m3S r c M)=m3 r c (Ev x y z M):=by
 simp only[m3S,p3S,m3,PV,Ev,Q8,Np];ring
lemma acg (x y z:ℂ) (M N:MS):Ev x y z (QI M N)=Ev x y z M+ Ev x y z N:=by
 funext p;simp only[Ev,QI,Q8,A1]
lemma RW (x y z:ℂ) (B1 B2:MS):ew x y z (PS B1 B2)=p4 (Bm+ Ev x y z B1+ Ev x y z B2)-65:=by
 have e:Ev x y z (QI (QI BmS B1) B2)=Bm+ Ev x y z B1+ Ev x y z B2:=by
  funext p;simp only[Ev,QI,Q8,ajF,A1]
 rw[PS,Q8,aju,QG,e];push_cast;ring
def aeE (x y z:ℂ):ew x y z (Vq 0)=x/\ew x y z (Vq 1)=y/\ew x y z (Vq 2)=z:=by
 simp[Vq,ew,ly,gn,ld]
def EvB (a b c:Fin 10) (x y z:ℂ):Ev x y z (SB a)=aq 2 3 (iz a) (mr a) x/\
  Ev x y z (SE b)=aq 1 3 (iz b) (mr b) y/\Ev x y z (SF c)=aq 1 2 (iz c) (mr c) z:=by
 obtain⟨d,e,f⟩:=aeE x y z;refine⟨?_,?_,?_⟩<;>funext p<;>simp only[Ev,SB,SE,SF,abS,d,e,f]
def akX (a b A B:ℤ) (q:ℂ) (h:(A:ℂ)+ B*q≠0) (e:a*B=b*A) (h2:a≠0\/b≠0):
  (a:ℂ)+ b*q≠0:=by
 intro g
 have f:(a:ℂ)*B=b*A:=by exact_mod_cast e
 have c:(b:ℂ)*(A+ B*q)=0:=by grind
 have d:(a:ℂ)*(A+ B*q)=0:=by grind
 rcases h2 with h2 | h2
 .exact h2 (by exact_mod_cast (A0.1 d).resolve_right h)
 .exact h2 (by exact_mod_cast (A0.1 c).resolve_right h)
lemma Uz (a b:Fin 10) (x y z:ℂ) (e:x≠0) (n2:x*MU 3 (mr a)- MU 3 (iz a)≠0)
  (i:MU 2 (iz a)+ x*MU 2 (mr a)≠0) (f:y≠0) (j:y*MU 3 (mr b)- MU 3 (iz b)≠0)
  (k:MU 1 (iz b)+ y*MU 1 (mr b)≠0):
  ∀ l:List (Nat× ℤ× ℤ),l.all (nzK a b)=true ->ew x y z (M6 l)≠0
 | [],_=> by simp[M6,ew,ly,gn,ld]
 | ⟨v,al,c⟩::l,h=> by
  simp only[List.all_cons,D8]at h
  show ew x y z (Iu (aa0 v al c) (M6 l))≠0
  rw[Np];refine mul_ne_zero ?_ (Uz a b x y z e n2 i f j k l h.2);have h1:=h.1;simp only[nzK,pr,D8,Bool.or_eq_true,L4,D7,beq_iff_eq]at h1;obtain⟨u,h1⟩:=h1;have g:∀ q:ℂ,q≠0-> ∀ A B:ℤ,(A:ℂ)+ B*q≠0->(al*B=c*A\/al=0)->
    (al:ℂ)+ c*q≠0:=by
   intro q t A B hAB hc;rcases hc with hc | hc
   .exact akX al c A B q hAB hc (by tauto)
   .subst hc
    have s:c≠0:=by tauto
    simp only[N2,C0]
    exact mul_ne_zero (by exact_mod_cast s) t
  have r:ew x y z (aa0 v al c)=(al:ℂ)+ c*(if v=0 then x else y):=by
   unfold aa0;split_ifs<;>simp[ew,ly,gn,ld]<;>ring
  rw[r];rw[Va,Va]at n2 i j k
  have m:((-o5 3 (iz a):ℤ):ℂ)+(o5 3 (mr a):ℤ)*x≠0:=by
   push_cast;intro d;exact n2 (by linear_combination d)
  have n:((o5 2 (iz a):ℤ):ℂ)+(o5 2 (mr a):ℤ)*x≠0:=by
   intro d;exact i (by linear_combination d)
  have o:((-o5 3 (iz b):ℤ):ℂ)+(o5 3 (mr b):ℤ)*y≠0:=by
   push_cast;intro d;exact j (by linear_combination d)
  have p:((o5 1 (iz b):ℤ):ℂ)+(o5 1 (mr b):ℤ)*y≠0:=by
   intro d;exact k (by linear_combination d)
  split_ifs with hv
  .rcases h1 with (h1 | ⟨-,h1 | h1⟩) | ⟨h1,-⟩
   .exact g x e 0 1 (by simpa using e) (Or.inr h1)
   .exact g x e _ _ m (Or.inl h1)
   .exact g x e _ _ n (Or.inl h1)
   .exact absurd hv h1
  .rcases h1 with (h1 | ⟨h1,-⟩) | ⟨-,h1 | h1⟩
   .exact g y f 0 1 (by simpa using f) (Or.inr h1)
   .exact absurd h1 hv
   .exact g y f _ _ o (Or.inl h1)
   .exact g y f _ _ p (Or.inl h1)
def Nw (a b c:Fin 10) (d:Fq) (k:ℤ) (e w:Nat) (F:P3) (Km l:List (Nat× ℤ× ℤ))
  (C:fBc a b c d k e w F Km l=true)
  (B:∀ q1 q2 q3:ℂ,q1≠0->q1*MU 3 (mr a)- MU 3 (iz a)≠0->MU 2 (iz a)+ q1*MU 2 (mr a)≠0->
   q2≠0->q2*MU 3 (mr b)- MU 3 (iz b)≠0->MU 1 (iz b)+ q2*MU 1 (mr b)≠0->
   q3≠0->q3*MU 2 (mr c)- MU 2 (iz c)≠0->MU 1 (iz c)+ q3*MU 1 (mr c)≠0->
   QH (aq 2 3 (iz a) (mr a) q1) (aq 1 3 (iz b) (mr b) q2) (aq 1 2 (iz c) (mr c) q3)->
   abm w q1 q2 q3=0->False):
  ∀ q1 q2 q3:ℂ,q1≠0->q1*MU 3 (mr a)- MU 3 (iz a)≠0->MU 2 (iz a)+ q1*MU 2 (mr a)≠0->
   q2≠0->q2*MU 3 (mr b)- MU 3 (iz b)≠0->MU 1 (iz b)+ q2*MU 1 (mr b)≠0->
   q3≠0->q3*MU 2 (mr c)- MU 2 (iz c)≠0->MU 1 (iz c)+ q3*MU 1 (mr c)≠0->
   QH (aq 2 3 (iz a) (mr a) q1) (aq 1 3 (iz b) (mr b) q2) (aq 1 2 (iz c) (mr c) q3)->False:=by
 intro x y z f g i j p q E T U A;by_cases D:abm w x y z=0
 .exact B x y z f g i j p q E T U A D
 obtain⟨K,u,v,S⟩:=A;simp only[fBc,D8,L4,D7,N5]at C;obtain⟨⟨⟨⟨⟨⟨⟨⟨P,R⟩,Z⟩,G⟩,H⟩,t12⟩,M⟩,N⟩,r⟩:=C;obtain⟨m,n,o⟩:=EvB a b c x y z
 have Q:ew x y z (PS (SB a) (SE b))=0:=by rw[RW,m,n,K,G4]
 have J:ew x y z (PS (SB a) (SF c))=0:=by rw[RW,m,o,u,G4]
 have V:ew x y z (PS (SE b) (SF c))=0:=by rw[RW,n,o,v,G4]
 have L:ew x y z (m3S 0 d (QI (QI (SB a) (SE b)) (SF c)))=0:=by
  rw[ajf,acg,acg,m,n,o];exact S d
 have t:ew x y z (aef e)≠0:=by
  obtain⟨W,X,Y⟩:=aeE x y z;unfold aef
  rcases (show e=0\/e=1\/e=2\/e=3 by omega) with h | h | h | h<;>subst h<;>
   simp[QG,W,X,Y,f,j,E]
 have s:ew x y z (aee w)=abm w x y z:=by
  unfold aee abm;split_ifs<;>simp[Cs,ew,ly,gn,ld]<;>ring
 have O:ew x y z F=0:=by
  have h0:=LD _ _ P x y z;rw[L,Np,Np,Np,QG,s]at h0;rcases A0.1 h0.symm with h | h
  .rcases A0.1 h with h | h
   .rcases A0.1 h with h | h
    .exact absurd (by exact_mod_cast h) R
    .exact absurd h t
   .exact absurd h D
  .exact h
 refine XJ F _ _ _ Km l (TtS a) 3 r x y z O ?_ ?_ ?_
  (Uz a b x y z f g i j p q Km M) (Uz a b x y z f g i j p q l N) ?_
 .rw[LD _ _ G];exact J
 .rw[LD _ _ H];exact V
 .rw[LD _ _ t12];exact Q
 .have q1:gn x [0,1]=x:=by simp[gn,ld]
  have q2:gn x [-o5 3 (iz a),o5 3 (mr a)]=x*MU 3 (mr a)- MU 3 (iz a):=by
   simp[gn,ld,Va]<;>ring
  have q3:gn x [o5 2 (iz a),o5 2 (mr a)]=MU 2 (iz a)+ x*MU 2 (mr a):=by
   simp[gn,ld,Va]<;>ring
  have :ew x y z (lx (TtS a))=
    (gn x [0,1]*gn x [-o5 3 (iz a),o5 3 (mr a)]*gn x [o5 2 (iz a),o5 2 (mr a)])^4:=by
   simp only[lx,TtS,ew,ly,ld,Rz,Lj,C3,B8]
  rw[this,q1,q2,q3];exact N4 4 (mul_ne_zero (mul_ne_zero f g) i)
def agZ (a b c:ℂ) (q:a≠0) (i:a*11-11≠0) (n:11+ a*11≠0) (o:b≠0) (j:b*11-11≠0) (m:11+ b*16≠0) (p:c≠0) (k:c*16-11≠0) (l:11+ c*11≠0)
  (h:QH (aq 2 3 0 1 a) (aq 1 3 0 1 b) (aq 1 2 0 2 c)) (r:a- b=0):False:=by
 obtain⟨MQ,e,f,d⟩:=h;have g:=d 3;clear d;simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at MQ e f g;grind
def ag0 (a b c:ℂ) (q:a≠0) (i:a*11-11≠0) (n:11+ a*11≠0) (o:b≠0) (j:b*11-11≠0) (m:11+ b*16≠0) (p:c≠0) (k:c*11-11≠0) (l:11+ c*11≠0)
  (h:QH (aq 2 3 0 1 a) (aq 1 3 0 1 b) (aq 1 2 0 3 c)) (r:a- b=0):False:=by
 obtain⟨g,e,f,d⟩:=h;have Me:=d 2;clear d;simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at g e f Me;grind
def ag1 (a b c:ℂ) (q:a≠0) (i:a*11-11≠0) (n:11+ a*11≠0) (o:b≠0) (j:b*11-11≠0) (m:11+ b*16≠0) (p:c≠0) (k:c*16-11≠0) (l:16+ c*11≠0)
  (h:QH (aq 2 3 0 1 a) (aq 1 3 0 1 b) (aq 1 2 1 2 c)) (r:a- b=0):False:=by
 obtain⟨MQ,e,f,d⟩:=h;have g:=d 3;clear d;simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at MQ e f g;grind
def ag2 (a b c:ℂ) (q:a≠0) (i:a*11-11≠0) (n:11+ a*11≠0) (o:b≠0) (j:b*11-11≠0) (m:11+ b*16≠0) (p:c≠0) (k:c*11-11≠0) (l:16+ c*11≠0)
  (h:QH (aq 2 3 0 1 a) (aq 1 3 0 1 b) (aq 1 2 1 3 c)) (r:a- b=0):False:=by
 obtain⟨g,e,f,d⟩:=h;have Me:=d 2;clear d;simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at g e f Me;grind
def Se:(∀ (c b a:ℂ) (l:c≠0) (d:c*11-11≠0) (i:11+ c*11≠0) (j:b≠0) (e:b*11-11≠0) (Ij:16+ b*11≠0) (k:a≠0) (f:a*16-11≠0) (g:16+ a*11≠0) (h:QH (aq 2 3 0 1 c) (aq 1 3 1 2 b) (aq 1 2 1 2 a)) (m:b- a=0),False)/\(∀ (c b a:ℂ) (l:c≠0) (d:c*11-11≠0) (i:11+ c*16≠0) (j:b≠0) (e:b*11-11≠0) (Ij:11+ b*16≠0) (k:a≠0) (f:a*11-11≠0) (g:11+ a*16≠0) (h:QH (aq 2 3 0 2 c) (aq 1 3 0 1 b) (aq 1 2 0 1 a)) (m:b- a=0),False)/\(∀ (c b a:ℂ) (l:c≠0) (d:c*11-11≠0) (i:11+ c*16≠0) (j:b≠0) (e:b*11-11≠0) (Ij:16+ b*11≠0) (k:a≠0) (f:a*16-11≠0) (g:11+ a*11≠0) (h:QH (aq 2 3 0 2 c) (aq 1 3 1 2 b) (aq 1 2 0 2 a)) (m:c+ a=0),False)/\(∀ (c b a:ℂ) (l:c≠0) (d:c*11-11≠0) (i:11+ c*16≠0) (j:b≠0) (e:b*11-11≠0) (Ij:16+ b*11≠0) (k:a≠0) (f:a*16-11≠0) (g:16+ a*11≠0) (h:QH (aq 2 3 0 2 c) (aq 1 3 1 2 b) (aq 1 2 1 2 a)) (m:b- a=0),False):=by
 refine⟨?_,?_,?_,?_⟩<;>intro c b a l d i j e Ij k f g h m;all_goals
  obtain⟨r,o,p,n⟩:=h
  have q:=n 3;clear n
  simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at r o p q
  grind
def af8 (c a b:ℂ) (q:c≠0) (i:c*11-11≠0) (n:11+ c*16≠0) (o:a≠0) (j:a*16-11≠0) (m:11+ a*11≠0) (p:b≠0) (k:b*11-16≠0) (l:11+ b*11≠0)
  (h:QH (aq 2 3 0 2 c) (aq 1 3 2 3 a) (aq 1 2 2 3 b)) (r:a- b=0):False:=by
 obtain⟨MQ,f,g,d⟩:=h;have e:=d 1;clear d;simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at MQ f g e;grind
def Ub:(∀ (a b c:ℂ) (l:a≠0) (d:a*11-11≠0) (i:11+ a*16≠0) (j:b≠0) (e:b*11-11≠0) (Ij:16+ b*11≠0) (k:c≠0) (f:c*11-11≠0) (g:16+ c*11≠0) (h:QH (aq 2 3 1 2 a) (aq 1 3 1 2 b) (aq 1 2 1 3 c)) (m:a- b=0),False)/\(∀ (a b c:ℂ) (l:a≠0) (d:a*11-11≠0) (i:11+ a*16≠0) (j:b≠0) (e:b*16-11≠0) (Ij:16+ b*11≠0) (k:c≠0) (f:c*16-11≠0) (g:16+ c*11≠0) (h:QH (aq 2 3 1 2 a) (aq 1 3 1 3 b) (aq 1 2 1 2 c)) (m:a+ c=0),False)/\(∀ (a b c:ℂ) (l:a≠0) (d:a*11-11≠0) (i:11+ a*16≠0) (j:b≠0) (e:b*16-11≠0) (Ij:16+ b*11≠0) (k:c≠0) (f:c*11-11≠0) (g:16+ c*11≠0) (h:QH (aq 2 3 1 2 a) (aq 1 3 1 3 b) (aq 1 2 1 3 c)) (m:b- c=0),False):=by
 refine⟨?_,?_,?_⟩<;>intro a b c l d i j e Ij k f g h m;all_goals
  obtain⟨q,o,p,n⟩:=h
  have r:=n 0;clear n
  simp +decide only[p4,m3,PV,aq,MU,E,Bm,A1,A4,A5,A9,A8]at q o p r
  grind
def mz {a b:ℂ} (h:a*b=0) (ha:a≠0):b=0:=(A0.1 h).resolve_left ha
set_option maxHeartbeats 0 in
def lM:ak 4 4 9/\ak 4 5 6/\ak 4 5 8/\ak 4 6 5/\ak 4 6 7/\ak 4 6 9/\ak 4 7 8/\ak 4 7 9/\ak 4 8 7/\ak 4 8 9/\ak 4 9 9/\ak 5 4 8/\ak 5 6 4/\ak 5 6 7/\ak 5 6 8/\ak 5 7 8/\ak 5 7 9/\ak 5 8 5/\ak 5 8 7/\ak 5 8 8/\ak 5 8 9/\ak 5 9 7/\ak 5 9 8:=by
 and_intros<;>refine SH _ _ _ ?_<;>
  rintro m a k b l c ⟨f,n⟩ ⟨d,o⟩ ⟨e,p⟩ q r s t u v g h i j<;>
  simp only[ahF,ahG,ahH,ahI,ahJ,ahK,p4,m3,PV,Q9,E,Bm,A1,A4,A5]at * <;>
  norm_num at *
 .have :(m- k)*(a*c+ b)=0:=mz (by linear_combination i) e;have :(m- k)*(a*c- b)=0:=(by linear_combination -j);grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination i) f) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -j) f) d;grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination i) f) e;have :(a*c- b)=0:=mz (by linear_combination j) d;grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -i) f) d;have :(a*c+ b)=0:=mz (mz (by linear_combination j) f) e;grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c+ b)=0:=mz (mz (by linear_combination j) f) e;grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c- b)=0:=mz (by linear_combination h) d;have :(a*c+ b)=0:=mz (mz (by linear_combination i) f) e;have :(a*c- b)=0:=mz (by linear_combination -j) f;grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination -i) e;have :(a*c- b)=0:=mz (by linear_combination j) d;grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination -i) e;have :(a*c+ b)=0:=(by linear_combination j);grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c- b)=0:=mz (by linear_combination -j) e;grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c- b)=0:=mz (by linear_combination h) d;have :(a*c- b)=0:=mz (by linear_combination -i) e;have :(a*c+ b)=0:=(by linear_combination j);grind
 .have :(k- l)*(a*c+ b)=0:=mz (by linear_combination -g) f;have :(k- l)*(a*c- b)=0:=(by linear_combination h);grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination h) f) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -i) d) e;have :(a*c- b)=0:=mz (by linear_combination -j) f;grind
 .have :(a*c- b)=0:=mz (mz (mz (by linear_combination g) f) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) f) d;have :(a*c+ b)=0:=mz (mz (by linear_combination -i) d) e;have :(a*c+ b)=0:=mz (mz (by linear_combination j) f) e;grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c- b)=0:=mz (by linear_combination -j) f;grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c+ b)=0:=mz (mz (by linear_combination h) f) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c- b)=0:=mz (by linear_combination -j) f;grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination g) f) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination -i) e;have :(a*c- b)=0:=mz (by linear_combination j) d;grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination g) f) e;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination -i) e;have :(a*c+ b)=0:=(by linear_combination j);grind
 .have :(m+ l)*(a*c+ b)=0:=mz (by linear_combination -h) d;have :(m+ l)*(a*c- b)=0:=(by linear_combination -j);grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c- b)=0:=mz (by linear_combination -j) e;grind
 .have :(k- l)*(a*c+ b)=0:=mz (by linear_combination -g) f;have :(k- l)*(a*c- b)=0:=(by linear_combination i);grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination g) f) e;have :(a*c- b)=0:=mz (by linear_combination h) d;have :(a*c- b)=0:=mz (by linear_combination -i) e;have :(a*c+ b)=0:=(by linear_combination j);grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c+ b)=0:=mz (mz (by linear_combination -h) d) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c+ b)=0:=(by linear_combination j);grind
 .have :(a*c+ b)=0:=mz (mz (by linear_combination -g) f) d;have :(a*c- b)=0:=mz (by linear_combination -h) e;have :(a*c- b)=0:=mz (by linear_combination i) d;have :(a*c+ b)=0:=(by linear_combination j);grind
set_option maxHeartbeats 0 in
def lE0:ak 4 4 0/\ak 4 4 1/\ak 4 4 2/\ak 4 4 3/\ak 4 5 0/\ak 4 5 1/\ak 4 5 3/\ak 4 6 0/\ak 4 6 1/\ak 4 6 2/\ak 4 6 3/\ak 4 7 0/\ak 4 7 1/\ak 4 7 2/\ak 4 7 3/\ak 4 8 0/\ak 4 8 1/\ak 4 8 2/\ak 4 8 3/\ak 4 9 0/\ak 4 9 1/\ak 4 9 2/\ak 4 9 3/\ak 4 0 0/\ak 4 0 1/\ak 4 0 2/\ak 4 0 3/\ak 4 1 1/\ak 4 1 2/\ak 4 1 3/\ak 4 2 2/\ak 4 2 3/\ak 4 3 2/\ak 5 4 0/\ak 5 4 1/\ak 5 4 3/\ak 5 6 0/\ak 5 6 1/\ak 5 6 2/\ak 5 6 3/\ak 5 7 0/\ak 5 7 1/\ak 5 7 2/\ak 5 7 3/\ak 5 8 0/\ak 5 8 1/\ak 5 8 2/\ak 5 8 3/\ak 5 9 0/\ak 5 9 1/\ak 5 9 2/\ak 5 9 3/\ak 5 0 5/\ak 5 0 7/\ak 5 0 8/\ak 5 0 9/\ak 5 0 0/\ak 5 0 1/\ak 5 0 2/\ak 5 0 3/\ak 5 1 5/\ak 5 1 7/\ak 5 1 8/\ak 5 1 9/\ak 5 1 0/\ak 5 1 1/\ak 5 1 2/\ak 5 1 3/\ak 5 2 5/\ak 5 2 7/\ak 5 2 8/\ak 5 2 9/\ak 5 2 0/\ak 5 2 1/\ak 5 2 2/\ak 5 2 3/\ak 5 3 7/\ak 5 3 8/\ak 5 3 9/\ak 5 3 0/\ak 5 3 1/\ak 5 3 2/\ak 5 3 3/\ak 7 7 0/\ak 7 7 1/\ak 7 7 3/\ak 7 8 0/\ak 7 8 1/\ak 7 8 2/\ak 7 8 3/\ak 7 9 0/\ak 7 9 1/\ak 7 9 2/\ak 7 9 3/\ak 7 0 7/\ak 7 0 9/\ak 7 0 0/\ak 7 0 1/\ak 7 0 2/\ak 7 0 3/\ak 7 1 7/\ak 7 1 9/\ak 7 1 0/\ak 7 1 1/\ak 7 1 2/\ak 7 1 3/\ak 7 2 7/\ak 7 2 9/\ak 7 2 0/\ak 7 2 1/\ak 7 2 2/\ak 7 2 3/\ak 7 3 7/\ak 7 3 0/\ak 7 3 1/\ak 7 3 2/\ak 7 3 3/\ak 9 8 0/\ak 9 8 1/\ak 9 8 3/\ak 9 0 0/\ak 9 0 1/\ak 9 0 2/\ak 9 0 3/\ak 9 1 1/\ak 9 1 2/\ak 9 1 3/\ak 9 2 2/\ak 9 2 3/\ak 9 3 2/\ak 0 0 1/\ak 0 0 3/\ak 0 1 1/\ak 0 1 2/\ak 0 1 3/\ak 0 2 2/\ak 0 2 3/\ak 0 3 2/\ak 1 1 2/\ak 1 1 3/\ak 1 2 3/\ak 1 3 2/\ak 2 1 1/\ak 2 3 1:=by
 and_intros<;>refine SH _ _ _ ?_<;>intros<;>dsimp +decide only[an7,an8,an9,aoa,ahF,ahG,ahH,ahI,ahJ,ahK,nz0,nz1,nz2,nz3,nz4,nz5,nz6,nz7,nz8,nz9,p4,m3,PV,M4,Q9,E,Bm,Pi.add_apply,Pi.smul_apply,smul_eq_mul,ite_true,ite_false]at * <;>grind
def fB0:ak 4 4 5:=
 fu 4 4 5 (by decide) (by decide) (by decide) (Nw 4 4 5 3 11 3 1 [[[0,-242],[297,-55]],[[-297,55],[-135,377]]] [(0,1,1)] [(1,11,16)] (by decide +kernel) agZ)
def fB1:ak 4 4 6:=
 fu 4 4 6 (by decide) (by decide) (by decide) (Nw 4 4 6 2 121 3 1 [[[0,-22],[27,-5]],[[-22],[-5,27]]] [(0,1,1)] [(1,11,16)] (by decide +kernel) ag0)
def fB2:ak 4 4 7:=
 fu 4 4 7 (by decide) (by decide) (by decide) (Nw 4 4 7 3 11 3 1 [[[-55,-297],[352]],[[-297,55],[-135,377]]] [(0,1,1)] [(1,11,16)] (by decide +kernel) ag1)
def fB3:ak 4 4 8:=
 fu 4 4 8 (by decide) (by decide) (by decide) (Nw 4 4 8 2 121 3 1 [[[-5,-27],[32]],[[-22],[-5,27]]] [(0,1,1)] [(1,11,16)] (by decide +kernel) ag2)
def anW:ak 4 7 7:=
 fu 4 7 7 (by decide) (by decide) (by decide) (Nw 4 7 7 3 (-11) 0 2 [[[352],[-55,-297]],[[-135,377],[-297,55]]] [(0,1,1)] [(1,16,11),(1,16,11)] (by decide +kernel) Se.1)
def anX:ak 5 4 4:=
 fu 5 4 4 (by decide) (by decide) (by decide) (Nw 5 4 4 3 (-297) 1 2 [[[0,-11],[11]],[[-11,-5],[0,16]]] [(0,11,16)] [(1,11,16),(1,11,16)] (by decide +kernel) Se.2.1)
def an0:ak 5 7 5:=
 fu 5 7 5 (by decide) (by decide) (by decide) (Nw 5 7 5 3 (-297) 0 3 [[[-11],[0,11]],[[5,-16],[11]]] [(0,11,16),(0,11,16)] [(1,16,11)] (by decide +kernel) Se.2.2.1)
def an1:ak 5 7 7:=
 fu 5 7 7 (by decide) (by decide) (by decide) (Nw 5 7 7 3 11 0 2 [[[-352,-80],[55,377]],[[135,-432],[297]]] [(0,11,16)] [(1,16,11),(1,16,11)] (by decide +kernel) Se.2.2.2)
def an2:ak 5 9 9:=
 fu 5 9 9 (by decide) (by decide) (by decide) (Nw 5 9 9 1 297 0 2 [[[-11],[0,16]],[[0,-11],[11,5]]] [(0,11,16)] [(1,1,1),(1,1,1)] (by decide +kernel) af8)
def akq:ak 7 7 8:=
 fu 7 7 8 (by decide) (by decide) (by decide) (Nw 7 7 8 0 297 3 1 [[[0,-16],[11,5]],[[-11],[0,11]]] [(0,11,16)] [(1,16,11)] (by decide +kernel) Ub.1)
def akr:ak 7 8 7:=
 fu 7 8 7 (by decide) (by decide) (by decide) (Nw 7 8 7 0 (-1) 2 3 [[[0,-4752],[4147,2765]],[[-4147,880],[0,4752]]] [(0,11,16),(0,11,16)] [(1,16,11)] (by decide +kernel) Ub.2.1)
def aks:ak 7 8 8:=
 fu 7 8 8 (by decide) (by decide) (by decide) (Nw 7 8 8 0 (-1) 1 2 [[[0,-4752],[4147,2765]],[[-3267],[605,4147]]] [(0,11,16)] [(1,16,11),(1,16,11)] (by decide +kernel) Ub.2.2)
def anU:ak 4 5 7:=
 fu 4 5 7 (by decide) (by decide) (by decide) (Nw 4 5 7 3 121 0 0 [[[],[-27,-5],[5,27]],[[0,-5,-27],[5,0,5],[27,-5]],[[0,-27,5],[0,-5,27]]] [(0,1,1)] [(1,1,1)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def anV:ak 4 6 8:=
 fu 4 6 8 (by decide) (by decide) (by decide) (Nw 4 6 8 2 11 0 0 [[[],[-297,-55],[135,377]],[[0,-55,-297],[0,135,135],[297,55]],[[0,-242],[0,55,297]]] [(0,1,1)] [(1,1,1)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def anY:ak 5 4 7:=
 fu 5 4 7 (by decide) (by decide) (by decide) (Nw 5 4 7 3 11 0 0 [[[0,297,135],[0,0,-432]],[[0,-55,352],[55,0,80],[-352,-80]],[[],[297],[135,-432]]] [(0,11,16)] [(1,11,16)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def anZ:ak 5 6 9:=
 fu 5 6 9 (by decide) (by decide) (by decide) (Nw 5 6 9 1 11 0 0 [[[],[-297],[0,432]],[[0,55,-352],[0,55,80],[297,135]],[[0,-242,-55],[0,55,377]]] [(0,11,16)] [(1,1,1)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def akt:ak 7 8 9:=
 fu 7 8 9 (by decide) (by decide) (by decide) (Nw 7 8 9 0 11 0 0 [[[],[-377,80],[0,432]],[[0,135,-432],[55,0,80],[297,135]],[[0,-297],[0,55,377]]] [(0,11,16)] [(1,16,11)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def aku:ak 7 9 8:=
 fu 7 9 8 (by decide) (by decide) (by decide) (Nw 7 9 8 0 (-1) 0 0 [[[],[0,-605,-4147],[0,4147,2765]],[[-3267,-1485],[1485,2765,-605],[0,605,4147]],[[0,-3267],[3267,1485]]] [(0,0,1),(0,11,16)] [(1,1,1)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def akv:ak 9 8 7:=
 fu 9 8 7 (by decide) (by decide) (by decide) (Nw 9 8 7 0 1 0 0 [[[],[-4752,880],[2765,4752]],[[0,-880,-4752],[880,0,880],[4752,-880]],[[0,-4752,2765],[0,880,4752]]] [(0,0,1),(0,16,11)] [(1,16,11),(1,0,1)] (by decide +kernel) (λ_ _ _ _ _ _ _ _ _ _ _ _ _ h=> A7 h))
def lC:ak 4 4 5/\ak 4 4 6/\ak 4 4 7/\ak 4 4 8/\ak 4 7 7/\ak 5 4 4/\ak 5 7 5/\ak 5 7 7/\ak 5 9 9/\ak 7 7 8/\ak 7 8 7/\ak 7 8 8/\ak 4 5 7/\ak 4 6 8/\ak 5 4 7/\ak 5 6 9/\ak 7 8 9/\ak 7 9 8/\ak 9 8 7:=
 ⟨fB0,fB1,fB2,fB3,anW,anX,an0,an1,an2,akq,akr,aks,anU,anV,anY,anZ,akt,aku,akv⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
def Ws:∀ i:Fin 186,ak (rA i) (rB i) (rC i):=by
 have :=lM;have :=lC;have :=lE0;casesm*_/\_;intro i;fin_cases i<;>dsimp only[rA,rB,rC,Nat.reducePow,Nat.reduceDiv,Nat.reduceMod,Fin.reduceOfNat]<;>assumption
def Kp (L:Sq) (r s:Fq):Sq:=Ar L r ⊓ Ar L s
lemma Kd (L:Sq) (r s:Fq) (X:Mt):
  X∈Kp L r s↔X∈L/\(∀ j,X (r,j)=0)/\(∀ j,X (s,j)=0):=by
 simp only[Kp,A6,ei];tauto
lemma Lk (L:Sq) (r s:Fq):Kp L r s=Kp L s r:=inf_comm _ _
def UK (L:Sq): Prop :=
 ∀ u:Fq,∀ X∈L,(∀ i j,i≠u->X (i,j)=0)->X=0
def CS (X:Mt) (j:Fq): Prop := ∃ i,X (i,j)≠0
def aco (r s t u:Fq) (a:r≠s) (b:r≠t) (c:r≠u) (d:s≠t) (e:s≠u)
  (f:t≠u):∀ i:Fq,i=r\/i=s\/i=t\/i=u:=by
 revert r s t u;decide +kernel
lemma O1 (t u:Fq) (a:Fin 10) (X:Mt) (h:ot t u a X) (j:Fq):
  CS X j↔(if a.val<4 then j=iz a else (j=iz a\/j=mr a)):=by
 by_cases g:a.val<4
 .simp only[ot,g,A9]at h ⊢;obtain⟨f,b,-⟩:=h;constructor
  .rintro⟨i,d⟩;by_contra e;exact d (f i j (λc=> e c.2))
  .rintro rfl;exact⟨t,b⟩
 .simp only[ot,g,A8]at h ⊢;obtain⟨f,b,h2,-,-,-⟩:=h;constructor
  .rintro⟨i,d⟩;by_contra e;exact d (f i j (λc=> e c.2))
  .rintro (rfl | rfl)
   .exact⟨t,b⟩
   .exact⟨t,h2⟩
def Mi (t u:Fq) (g:Fin 10) (X:Mt) (h:ot t u g X) (j:Fq):
  (CS X j↔X (t,j)≠0)/\(CS X j↔X (u,j)≠0):=by
 rw[O1 t u g X h j];by_cases Iq:g.val<4
 .simp only[ot,Iq,A9]at h ⊢;obtain⟨d,e,f⟩:=h;refine⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  .rintro rfl;exact e
  .intro c;by_contra b;exact c (d t j (λa=> b a.2))
  .rintro rfl;exact f
  .intro c;by_contra b;exact c (d u j (λa=> b a.2))
 .simp only[ot,Iq,A8]at h ⊢;obtain⟨d,e,f,i,k,-⟩:=h;refine⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  .rintro (rfl | rfl)
   .exact e
   .exact f
  .intro c;by_contra b;exact c (d t j (λa=> b a.2))
  .rintro (rfl | rfl)
   .exact i
   .exact k
  .intro c;by_contra b;exact c (d u j (λa=> b a.2))
def OZ (K:Sq) (d:finrank ℂ K=1) (g:Mt) (a:g∈K)
  (b:g≠0):∀ Y∈K,∃ c:ℂ,Y=c•g:=by
 intro Y e
 have hv:(⟨g,a⟩:K)≠0:=by
  intro h;apply b;simpa using congrArg Subtype.val h
 obtain⟨c,f⟩:=(finrank_eq_one_iff_of_nonzero' (⟨g,a⟩:K) hv).1 d ⟨Y,e⟩
 exact⟨c,by simpa using (congrArg Subtype.val f).symm⟩
def TE (L:Sq) (f:∀ t∈L,p4 (Bm+ t)=65) (e:finrank ℂ L=6)
  (r s:Fq) (d:r≠s):1≤ finrank ℂ (Kp L r s):=by
 obtain⟨X,g,c,h,i⟩:=Zv L f e r s d;have b:X∈Kp L r s:=(Kd L r s X).2 ⟨g,h,i⟩;by_contra j
 have a:finrank ℂ (Kp L r s)=0:=by omega
 rw[Submodule.finrank_eq_zero]at a;rw[a]at b;exact c ((L5 ℂ).1 b)
def LI (L:Sq) (C:∀ t∈L,p4 (Bm+ t)=65) (B:finrank ℂ L=6)
  (x:∀ r,finrank ℂ (L.map (af r))=3) (m:UK L)
  (r s t u:Fq) (p:r< s) (k:t< u) (q:r≠t) (v:r≠u) (w:s≠t) (n:s≠u)
  (F:finrank ℂ (Kp L r s)=1) (g:Mt) (y:g∈Kp L r s) (c:g≠0):
  ∃ G,ot t u G g:=by
 obtain⟨Zj,d,e⟩:=(Kd L r s g).1 y;have o:=OZ _ F g y c;have D:=N1 L C B r s t u p k q v w n (x r) (x s) g Zj d e c
  (λY E z A=> o Y ((Kd L r s Y).2 ⟨E,z,A⟩))
 have f:=aco r s t u (D5 p) q v w n (D5 k);apply SR;apply XH t u (D5 k) g
 .intro i j b h;rcases f i with rfl | rfl | rfl | rfl
  .exact d j
  .exact e j
  .exact absurd rfl b
  .exact absurd rfl h
 .exact Z8 t u g D
 .by_contra a;apply c;apply m u g Zj;intro i j h;rcases f i with rfl | rfl | rfl | rfl
  .exact d j
  .exact e j
  .by_contra l;exact a ⟨j,l⟩
  .exact absurd rfl h
 .by_contra a;apply c;apply m t g Zj;intro i j b;rcases f i with rfl | rfl | rfl | rfl
  .exact d j
  .exact e j
  .exact absurd rfl b
  .by_contra l;exact a ⟨j,l⟩
def aeD (Kg:∀ i:Fin 186,ak (rA i) (rB i) (rC i))
  (L:Sq) (e:∀ t∈L,p4 (Bm+ t)=65) (l:finrank ℂ L=6)
  (d:∀ r,finrank ℂ (L.map (af r))=3) (LG:UK L)
  (u:finrank ℂ (Kp L 0 1)=1) (s:finrank ℂ (Kp L 0 2)=1) (v:finrank ℂ (Kp L 0 3)=1)
  (b a c:Mt) (f:b∈Kp L 0 1) (g:a∈Kp L 0 2) (h:c∈Kp L 0 3)
  (x:b≠0) (y:a≠0) (z:c≠0):
  (∀ j,CS b j↔CS a j)/\(∀ j,CS a j↔CS c j):=by
 obtain⟨o,m⟩:=LI L e l d LG 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) u b f x
 obtain⟨k,H2⟩:=LI L e l d LG 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) s a g y
 obtain⟨p,n⟩:=LI L e l d LG 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) v c h z
 have w:Lq b a c:=Rh L e (d 0) b a c (A6.1 f).1
  (A6.1 g).1 (A6.1 h).1
 have Mq:o=k/\k=p:=by
  by_contra q;exact UN Kg o k p q b a c m H2 n w
 obtain⟨rfl,rfl⟩:=Mq
 exact⟨λj=> by rw[O1 _ _ _ _ m,O1 _ _ _ _ H2],
  λj=> by rw[O1 _ _ _ _ H2,O1 _ _ _ _ n]⟩
def Z5 (L:Sq) (a:Equiv.Perm Fq) (h:UK L):UK (L.map (gp a)):=by
 intro u Y f b;obtain⟨X,e,rfl⟩:=B6.1 f
 have :X=0:=by
  apply h (a.symm u) X e;intro i j g
  have d:=b (a i) (a j) (λc=> g (by rw[<- c];simp))
  simpa[my] using d
 rw[this,H5]
lemma ZD (a:Equiv.Perm Fq) (r:Fq):
  (af r).comp (gp a)=
   (LinearEquiv.funCongrLeft ℂ ℂ a.symm).toLinearMap.comp (af (a.symm r)):=by
 apply LinearMap.ext;intro X;funext j;simp[bu,my,LinearEquiv.funCongrLeft_apply]
def Pg (L:Sq) (b:Equiv.Perm Fq)
  (a:∀ r,finrank ℂ (L.map (af r))=3):∀ r,finrank ℂ ((L.map (gp b)).map (af r))=3:=by
 intro r;rw[<- H8,ZD,H8,L6];exact a _
lemma ab0 (L:Sq) (a:Equiv.Perm Fq) (r s:Fq):
  Kp (L.map (gp a)) (a r) (a s)=(Kp L r s).map (gp a):=by
 ext Y;rw[Kd,B6,B6];constructor
 .rintro⟨⟨X,b,rfl⟩,c,d⟩
  refine⟨X,(Kd L r s X).2 ⟨b,λj=> ?_,λj=> ?_⟩,rfl⟩
  .simpa[my] using c (a j)
  .simpa[my] using d (a j)
 .rintro⟨X,b,rfl⟩;obtain⟨e,c,d⟩:=(Kd L r s X).1 b
  exact⟨⟨X,e,rfl⟩,λj=> by simp[my,c],λj=> by simp[my,d]⟩
lemma abL (a:Equiv.Perm Fq) (X:Mt) (j:Fq):CS (gp a X) j↔CS X (a.symm j):=by
 constructor
 .rintro⟨i,b⟩;exact⟨a.symm i,by simpa[my] using b⟩
 .rintro⟨i,b⟩;exact⟨a i,by simpa[my] using b⟩
def agW (p:∀ i:Fin 186,ak (rA i) (rB i) (rC i))
  (L:Sq) (hL:∀ t∈L,p4 (Bm+ t)=65) (x:finrank ℂ L=6)
  (y:∀ r,finrank ℂ (L.map (af r))=3) (q:UK L)
  (a:Equiv.Perm Fq) (r f s2 s3:Fq) (w:a r=0) (e1:a f=1) (k:a s2=2)
  (l:a s3=3)
  (u:finrank ℂ (Kp L r f)=1) (LR:finrank ℂ (Kp L r s2)=1) (v:finrank ℂ (Kp L r s3)=1)
  (d b e:Mt) (m:d∈Kp L r f) (n:b∈Kp L r s2) (o:e∈Kp L r s3)
  (G:d≠0) (H:b≠0) (J:e≠0):
  (∀ j,CS d j↔CS b j)/\(∀ j,CS b j↔CS e j):=by
 have c:∀ s:Fq,Kp (L.map (gp a)) 0 (a s)=(Kp L r s).map (gp a):=by
  intro s;have :=ab0 L a r s;rw[w]at this;exact this
 have k1:finrank ℂ (Kp (L.map (gp a)) 0 1)=1:=by rw[<- e1,c,o6];exact u
 have C:finrank ℂ (Kp (L.map (gp a)) 0 2)=1:=by rw[<- k,c,o6];exact LR
 have D:finrank ℂ (Kp (L.map (gp a)) 0 3)=1:=by rw[<- l,c,o6];exact v
 have E:gp a d∈Kp (L.map (gp a)) 0 1:=by rw[<- e1,c];exact C4 m
 have F:gp a b∈Kp (L.map (gp a)) 0 2:=by rw[<- k,c];exact C4 n
 have K:gp a e∈Kp (L.map (gp a)) 0 3:=by rw[<- l,c];exact C4 o
 have z:∀ g:Mt,g≠0->gp a g≠0:=λg hg h=> hg (O5 a (by rw[h,H5]))
 obtain⟨A,B⟩:=aeD p (L.map (gp a)) (LY L hL a) (by rw[o6];exact x)
  (Pg L a y) (Z5 L a q) k1 C D _ _ _ E F K (z d G) (z b H) (z e J)
 refine⟨λj=> ?_,λj=> ?_⟩
 .have :=A (a j);simpa[abL] using this
 .have :=B (a j);simpa[abL] using this
def ZE (L:Sq) (k:finrank ℂ L=6) (l:∀ r,finrank ℂ (L.map (af r))=3)
  (c:UK L) (r s t u:Fq) (d:∀ i:Fq,i=r\/i=s\/i=t\/i=u)
  (h:2≤ finrank ℂ (Kp L r s)) (h2:2≤ finrank ℂ (Kp L r t)):False:=by
 obtain⟨X,m,e⟩:=Uy (Ar L r) (Kp L r s) (Kp L r t) (MF L k r (l r))
  inf_le_left inf_le_left h h2
 obtain⟨o,p⟩:=A6.1 m;obtain⟨f,n,a⟩:=(Kd L r s X).1 o;obtain⟨-,-,b⟩:=(Kd L r t X).1 p;apply e;apply c u X f;intro i j g;rcases d i with rfl | rfl | rfl | rfl
 .exact n j
 .exact a j
 .exact b j
 .exact absurd rfl g
def H6 (L:Sq) (e:finrank ℂ L=6) (f:∀ r,finrank ℂ (L.map (af r))=3)
  (r s t u:Fq) (h:2≤ finrank ℂ (Kp L r s)):
  finrank ℂ ((Kp L r t ⊔ Kp L r u).map (af s))≤1:=by
 have g:=MF L e r (f r);have c:=dx (Ar L r) (af s)
 have a:Ar L r ⊓ ker (af s)=Kp L r s:=by
  ext X;simp only[Kp,Ar,A6,C7];tauto
 have b:(Kp L r t ⊔ Kp L r u).map (af s)≤(Ar L r).map (af s):=
  P5 (sup_le inf_le_left inf_le_left)
 have d:=E7 b;rw[a]at c;omega
def Tz (x y:Fq->ℂ) (abh:∀ c d,x c*y d=x d*y c)
  (g:∃ k,x k≠0) (h:∃ k,y k≠0) (j:Fq):x j≠0↔y j≠0:=by
 obtain⟨k,e⟩:=g;obtain⟨l,f⟩:=h;constructor
 .intro b hyj;have a:=abh j l;rw[hyj,C3]at a;exact mul_ne_zero b f a
 .intro hyj b;have a:=abh k j;rw[b,F4]at a;exact mul_ne_zero e hyj a
def Yo (L:Sq) (m:finrank ℂ L=6) (n:∀ r,finrank ℂ (L.map (af r))=3)
  (r s t u:Fq) (v:2≤ finrank ℂ (Kp L r s))
  (g h:Mt) (p:g∈Kp L r t) (q:h∈Kp L r u) (g0:g≠0) (l:h≠0)
  (b:∀ j,CS g j↔g (s,j)≠0) (c:∀ j,CS h j↔h (s,j)≠0):∀ j,CS g j↔CS h j:=by
 have o:=H6 L m n r s t u v;have w:af s g∈(Kp L r t ⊔ Kp L r u).map (af s):=
  C4 (P7 p)
 have x:af s h∈(Kp L r t ⊔ Kp L r u).map (af s):=
  C4 (N6 q)
 have e:=LU _ o _ _ w x
 have f:∃ k,af s g k≠0:=by
  by_contra a;push_neg at a;apply g0;funext ⟨i,j⟩;by_contra d;exact ((b j).1 ⟨i,d⟩) (a j)
 have nzh:∃ k,af s h k≠0:=by
  by_contra a;push_neg at a;apply l;funext ⟨i,j⟩;by_contra d;exact ((c j).1 ⟨i,d⟩) (a j)
 intro j;rw[b j,c j];exact Tz _ _ e f nzh j
def Pc (a:Fin 10) (j:Fq): Prop :=if a.val<4 then j=iz a else (j=iz a\/j=mr a)
def agH:∀ b a:Fin 10,(∀ j:Fq,Pc b j↔Pc a j)->b=a:=by
 unfold Pc;decide +kernel
def Qz (t u d e:Fq) (b a:Fin 10) (X c:Mt) (h:ot t u b X) (f:ot d e a c)
  (g:∀ j,CS X j↔CS c j):b=a:=
 agH b a (λj=>(O1 t u b X h j).symm.trans ((g j).trans (O1 d e a c f j)))
def Sy:∀ a:Fin 10,¬ a.val<4->iz a< mr a:=by decide
def Rx (L:Sq) (h6:finrank ℂ L=6) (c:∀ r,finrank ℂ (L.map (af r))=3)
  (r s t u:Fq) (f:2≤ finrank ℂ (Kp L r s)) (g h:Mt) (d:g∈Kp L r t) (e:h∈Kp L r u):
  ∀ a b,g (s,a)*h (s,b)=g (s,b)*h (s,a):=
 LU _ (H6 L h6 c r s t u f) _ _
  (C4 (P7 d)) (C4 (N6 e))
lemma SO (L:Sq) (a:Equiv.Perm Fq) (r s b c:Fq) (d:a r=b) (e:a s=c):
  finrank ℂ (Kp (L.map (gp a)) b c)=finrank ℂ (Kp L r s):=by
 rw[<- d,<- e,ab0,o6]
def aaQ (L:Sq): Prop :=
 ∀ c:Fq,∀ Ks b a:Mt,Ks∈L->b∈L->a∈L->
  Mc 1 3 c Ks->Mc 1 2 c b->Mc 0 3 c a->False
def aaP (L:Sq): Prop :=
 ∀ c d:Fq,c< d-> ∀ e KQ g12 g13:Mt,e∈L->KQ∈L->g12∈L->g13∈L->
  Ke 1 3 c d e->Ke 1 2 c d KQ->Ke 0 3 c d g12->Ke 0 2 c d g13->
  (((∀ a b,e (1,a)*KQ (1,b)=e (1,b)*KQ (1,a))/\
    (∀ a b,g12 (0,a)*g13 (0,b)=g12 (0,b)*g13 (0,a)))\/ ∃ g∈L,Ke 2 3 c d g)->
  (((∀ a b,e (3,a)*g12 (3,b)=e (3,b)*g12 (3,a))/\
    (∀ a b,KQ (2,a)*g13 (2,b)=KQ (2,b)*g13 (2,a)))\/ ∃ f∈L,Ke 0 1 c d f)->False
def YB (Q:∀ i:Fin 186,ak (rA i) (rB i) (rC i))
    (L:Sq) (l:∀ t∈L,p4 (Bm+ t)=65) (f:finrank ℂ L=6)
    (hI:∀ r,finrank ℂ (L.map (af r))=3) (LG:UK L) (aA:aaQ L) (az:aaP L)
    (R:finrank ℂ (Kp L 0 2)=1) (XF:finrank ℂ (Kp L 0 3)=1)
    (D:finrank ℂ (Kp L 1 2)=1) (O:finrank ℂ (Kp L 1 3)=1):False:=by
  obtain⟨d,n,n02⟩:=dk (K:=Kp L 0 2) (by omega)
  obtain⟨KQ,o,J⟩:=dk (K:=Kp L 0 3) (by omega)
  obtain⟨g12,p,u⟩:=dk (K:=Kp L 1 2) (by omega)
  obtain⟨c,q,M⟩:=dk (K:=Kp L 1 3) (by omega)
  obtain⟨τ,m⟩:=LI L l f hI LG 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) R d n n02
  obtain⟨ao,w⟩:=LI L l f hI LG 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) XF KQ o J
  obtain⟨ap,T12⟩:=LI L l f hI LG 1 2 0 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) D g12 p u
  obtain⟨as,s⟩:=LI L l f hI LG 1 3 0 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) O c q M
  have ZS:=((Kd L 0 2 d).1 n).1;have ZT:=((Kd L 0 3 KQ).1 o).1;have N:=((Kd L 1 2 g12).1 p).1;have V:=((Kd L 1 3 c).1 q).1
  have aE:=TE L l f 0 1 (by decide)
  have aF:=TE L l f 2 3 (by decide)
  have T:(∀ j,CS d j↔CS KQ j)/\(∀ j,CS g12 j↔CS c j)/\
      (((∀ a b,d (1,a)*KQ (1,b)=d (1,b)*KQ (1,a))/\
        (∀ a b,g12 (0,a)*c (0,b)=g12 (0,b)*c (0,a)))\/
       ∃ k∈L,(∀ j,CS k j↔CS d j)/\ ∃ v,ot 2 3 v k):=by
    rcases (show 2≤ finrank ℂ (Kp L 0 1)\/finrank ℂ (Kp L 0 1)=1 by omega) with x | hb
    · have y:2≤ finrank ℂ (Kp L 1 0):=by rw[Lk];exact x
      exact⟨Yo L f hI 0 1 2 3 x d KQ n o n02 J (λj=>(Mi _ _ _ _ m j).1)
          (λj=>(Mi _ _ _ _ w j).1),
        Yo L f hI 1 0 2 3 y g12 c p q u M (λj=>(Mi _ _ _ _ T12 j).1)
          (λj=>(Mi _ _ _ _ s j).1),
        Or.inl ⟨Rx L f hI 0 1 2 3 x d KQ n o,Rx L f hI 1 0 2 3 y g12 c p q⟩⟩
    · obtain⟨k,z,H⟩:=dk (K:=Kp L 0 1) (by omega)
      obtain⟨am,B⟩:=LI L l f hI LG 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hb k z H
      have v0:=aeD Q L l f hI LG hb R XF k d KQ z n o H n02 J
      have al:k∈Kp L 1 0:=by rw[Lk];exact z
      have aB:finrank ℂ (Kp L 1 0)=1:=by rw[Lk];exact hb
      have v1:=agW Q L l f hI LG (swap 0 1) 1 0 2 3 (by decide) (by decide) (by decide)
        (by decide) aB D O k g12 c al p q H u M
      exact⟨v0.2,v1.2,Or.inr ⟨k,((Kd L 0 1 k).1 z).1,v0.1,am,B⟩⟩
  have QZ:(∀ j,CS d j↔CS g12 j)/\
      (((∀ a b,d (3,a)*g12 (3,b)=d (3,b)*g12 (3,a))/\
        (∀ a b,KQ (2,a)*c (2,b)=KQ (2,b)*c (2,a)))\/
       ∃ g∈L,(∀ j,CS d j↔CS g j)/\ ∃ v,ot 0 1 v g):=by
    have E:d∈Kp L 2 0:=by rw[Lk];exact n
    have F:g12∈Kp L 2 1:=by rw[Lk];exact p
    have aC:KQ∈Kp L 3 0:=by rw[Lk];exact o
    have aD:c∈Kp L 3 1:=by rw[Lk];exact q
    rcases (show 2≤ finrank ℂ (Kp L 2 3)\/finrank ℂ (Kp L 2 3)=1 by omega) with x | hb
    · have y:2≤ finrank ℂ (Kp L 3 2):=by rw[Lk];exact x
      exact⟨Yo L f hI 2 3 0 1 x d g12 E F n02 u (λj=>(Mi _ _ _ _ m j).2)
          (λj=>(Mi _ _ _ _ T12 j).2),
        Or.inl ⟨Rx L f hI 2 3 0 1 x d g12 E F,Rx L f hI 3 2 0 1 y KQ c aC aD⟩⟩
    · obtain⟨g,G,P⟩:=dk (K:=Kp L 2 3) (by omega)
      obtain⟨au,A⟩:=LI L l f hI LG 2 3 0 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hb g G P
      have aw:finrank ℂ (Kp L 2 1)=1:=by rw[Lk];exact D
      have av:finrank ℂ (Kp L 2 0)=1:=by rw[Lk];exact R
      have v2:=agW Q L l f hI LG (swap 0 2) 2 1 0 3 (by decide) (by decide) (by decide)
        (by decide) aw av hb g12 d g F E G u n02 P
      exact⟨λj=>(v2.1 j).symm,Or.inr ⟨g,((Kd L 2 3 g).1 G).1,v2.2,au,A⟩⟩
  obtain⟨ax,ag,Y⟩:=T;obtain⟨ae,Z⟩:=QZ;have ay:τ=ao:=Qz _ _ _ _ _ _ _ _ m w ax;have X:τ=ap:=Qz _ _ _ _ _ _ _ _ m T12 ae;have XI:τ=as:=X.trans (Qz _ _ _ _ _ _ _ _ T12 s ag);rw[<- ay]at w;rw[<- X]at T12;rw[<- XI]at s;by_cases C:τ.val<4
  · simp only[ot,C,A9]at m w T12
    exact aA (iz τ) d KQ g12 ZS ZT N m w T12
  · have ai:((∀ a b,d (1,a)*KQ (1,b)=d (1,b)*KQ (1,a))/\
        (∀ a b,g12 (0,a)*c (0,b)=g12 (0,b)*c (0,a)))\/ ∃ k∈L,Ke 2 3 (iz τ) (mr τ) k:=by
      rcases Y with h | ⟨k,U,S,v,B⟩
      .exact Or.inl h
      · have e:v= τ:=Qz _ _ _ _ _ _ _ _ B m S
        rw[e]at B
        simp only[ot,C,A8]at B
        exact Or.inr ⟨k,U,B⟩
    have aj:((∀ a b,d (3,a)*g12 (3,b)=d (3,b)*g12 (3,a))/\
        (∀ a b,KQ (2,a)*c (2,b)=KQ (2,b)*c (2,a)))\/ ∃ g∈L,Ke 0 1 (iz τ) (mr τ) g:=by
      rcases Z with h | ⟨g,W,S,v,A⟩
      .exact Or.inl h
      · have e:v= τ:=(Qz _ _ _ _ _ _ _ _ m A S).symm
        rw[e]at A
        simp only[ot,C,A8]at A
        exact Or.inr ⟨g,W,A⟩
    simp only[ot,C,A8]at m w T12 s
    exact az (iz τ) (mr τ) (Sy τ C) d KQ g12 c ZS ZT N V m w T12 s ai aj
def SR0 (y:∀ i:Fin 186,ak (rA i) (rB i) (rC i))
  (o:∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6->aaQ L)
  (n:∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6->aaP L)
  (L:Sq) (k:∀ t∈L,p4 (Bm+ t)=65) (f:finrank ℂ L=6)
  (x:∀ r,finrank ℂ (L.map (af r))=3) (p:UK L):False:=by
 have c:∀ r s:Fq,r≠s-> ¬ 2≤ finrank ℂ (Kp L r s)->finrank ℂ (Kp L r s)=1:=
  λr s h hn=> by have :=TE L k f r s h;omega
 have b:∀ r s t u:Fq,(∀ i:Fq,i=r\/i=s\/i=t\/i=u)->
   2≤ finrank ℂ (Kp L r s)->2≤ finrank ℂ (Kp L r t)->False:=
  λr s t u C A B=> ZE L f x p r s t u C A B
 have a:∀ r s:Fq,finrank ℂ (Kp L r s)=finrank ℂ (Kp L s r):=λr s=> by rw[Lk]
 have z:∀ d:Equiv.Perm (Fq),finrank ℂ (Kp (L.map (gp d)) 0 2)=1->
   finrank ℂ (Kp (L.map (gp d)) 0 3)=1->finrank ℂ (Kp (L.map (gp d)) 1 2)=1->
   finrank ℂ (Kp (L.map (gp d)) 1 3)=1->False:=by
  intro d l w b12 e;have Ly:=LY L k d
  have q:finrank ℂ (L.map (gp d))=6:=by rw[o6];exact f
  exact YB y (L.map (gp d)) Ly q (Pg L d x) (Z5 L d p)
   (o _ Ly q) (n _ Ly q) l w b12 e
 by_cases g:2≤ finrank ℂ (Kp L 0 2)\/2≤ finrank ℂ (Kp L 1 3)
 .have v:finrank ℂ (Kp L 0 1)=1:=c 0 1 (by decide) (λh=> by
   rcases g with h' | h'
   .exact b 0 1 2 3 (by decide) h h'
   .exact b 1 0 3 2 (by decide) (by rw[a];exact h) h')
  have w:finrank ℂ (Kp L 0 3)=1:=c 0 3 (by decide) (λh=> by
   rcases g with h' | h'
   .exact b 0 3 2 1 (by decide) h h'
   .exact b 3 0 1 2 (by decide) (by rw[a];exact h) (by rw[a];exact h'))
  have b12:finrank ℂ (Kp L 1 2)=1:=c 1 2 (by decide) (λh=> by
   rcases g with h' | h'
   .exact b 2 1 0 3 (by decide) (by rw[a];exact h) (by rw[a];exact h')
   .exact b 1 2 3 0 (by decide) h h')
  have j:finrank ℂ (Kp L 2 3)=1:=c 2 3 (by decide) (λh=> by
   rcases g with h' | h'
   .exact b 2 3 0 1 (by decide) h (by rw[a];exact h')
   .exact b 3 2 1 0 (by decide) (by rw[a];exact h) (by rw[a];exact h'))
  apply z (swap 1 2)
  .rw[SO L _ 0 1 0 2 (by decide) (by decide)];exact v
  .rw[SO L _ 0 3 0 3 (by decide) (by decide)];exact w
  .rw[SO L _ 2 1 1 2 (by decide) (by decide),a];exact b12
  .rw[SO L _ 2 3 1 3 (by decide) (by decide)];exact j
 .push_neg at g;obtain⟨D,G⟩:=g
  have l:finrank ℂ (Kp L 0 2)=1:=c 0 2 (by decide) (by omega)
  have e:finrank ℂ (Kp L 1 3)=1:=c 1 3 (by decide) (by omega)
  by_cases m:2≤ finrank ℂ (Kp L 0 3)\/2≤ finrank ℂ (Kp L 1 2)
  .have v:finrank ℂ (Kp L 0 1)=1:=c 0 1 (by decide) (λh=> by
    rcases m with h' | h'
    .exact b 0 1 3 2 (by decide) h h'
    .exact b 1 0 2 3 (by decide) (by rw[a];exact h) h')
   have j:finrank ℂ (Kp L 2 3)=1:=c 2 3 (by decide) (λh=> by
    rcases m with h' | h'
    .exact b 3 2 0 1 (by decide) (by rw[a];exact h) (by rw[a];exact h')
    .exact b 2 3 1 0 (by decide) h (by rw[a];exact h'))
   apply z (swap 1 3)
   .rw[SO L _ 0 2 0 2 (by decide) (by decide)];exact l
   .rw[SO L _ 0 1 0 3 (by decide) (by decide)];exact v
   .rw[SO L _ 3 2 1 2 (by decide) (by decide),a];exact j
   .rw[SO L _ 3 1 1 3 (by decide) (by decide),a];exact e
  .push_neg at m;obtain⟨E,F⟩:=m;exact YB y L k f x p (o L k f) (n L k f) l
    (c 0 3 (by decide) (by omega)) (c 1 2 (by decide) (by omega)) e
def WR:(∀ (a b c d:ℂ) (v:a≠0) (e:a*11-11≠0) (q:11+ a*11≠0) (t:b≠0) (f:b*16-11≠0) (p:11+ b*11≠0) (u:c≠0) (g:c*11-11≠0) (o:16+ c*11≠0) (s:d≠0) (h:d*16-11≠0) (r:16+ d*11≠0) (j:p4 (Bm+(aq 1 3 0 2 a)+(aq 1 2 0 2 b))=65) (i:p4 (Bm+(aq 1 3 0 2 a)+(aq 0 3 0 2 c))=65) (k:p4 (Bm+(aq 1 3 0 2 a)+(aq 0 2 0 2 d))=65) (n:p4 (Bm+(aq 1 2 0 2 b)+(aq 0 3 0 2 c))=65) (l:p4 (Bm+(aq 1 2 0 2 b)+(aq 0 2 0 2 d))=65) (m:p4 (Bm+(aq 0 3 0 2 c)+(aq 0 2 0 2 d))=65),False)/\(∀ (a b c d:ℂ) (v:a≠0) (e:a*16-11≠0) (q:11+ a*11≠0) (t:b≠0) (f:b*11-11≠0) (p:11+ b*11≠0) (u:c≠0) (g:c*16-11≠0) (o:16+ c*11≠0) (s:d≠0) (h:d*11-11≠0) (r:16+ d*11≠0) (j:p4 (Bm+(aq 1 3 0 3 a)+(aq 1 2 0 3 b))=65) (i:p4 (Bm+(aq 1 3 0 3 a)+(aq 0 3 0 3 c))=65) (k:p4 (Bm+(aq 1 3 0 3 a)+(aq 0 2 0 3 d))=65) (n:p4 (Bm+(aq 1 2 0 3 b)+(aq 0 3 0 3 c))=65) (l:p4 (Bm+(aq 1 2 0 3 b)+(aq 0 2 0 3 d))=65) (m:p4 (Bm+(aq 0 3 0 3 c)+(aq 0 2 0 3 d))=65),False)/\(∀ (a b c d:ℂ) (v:a≠0) (e:a*11-11≠0) (q:16+ a*11≠0) (t:b≠0) (f:b*16-11≠0) (p:16+ b*11≠0) (u:c≠0) (g:c*11-11≠0) (o:11+ c*11≠0) (s:d≠0) (h:d*16-11≠0) (r:11+ d*11≠0) (j:p4 (Bm+(aq 1 3 1 2 a)+(aq 1 2 1 2 b))=65) (i:p4 (Bm+(aq 1 3 1 2 a)+(aq 0 3 1 2 c))=65) (k:p4 (Bm+(aq 1 3 1 2 a)+(aq 0 2 1 2 d))=65) (n:p4 (Bm+(aq 1 2 1 2 b)+(aq 0 3 1 2 c))=65) (l:p4 (Bm+(aq 1 2 1 2 b)+(aq 0 2 1 2 d))=65) (m:p4 (Bm+(aq 0 3 1 2 c)+(aq 0 2 1 2 d))=65),False)/\(∀ (a b c d:ℂ) (v:a≠0) (e:a*16-11≠0) (q:16+ a*11≠0) (t:b≠0) (f:b*11-11≠0) (p:16+ b*11≠0) (u:c≠0) (g:c*16-11≠0) (o:11+ c*11≠0) (s:d≠0) (h:d*11-11≠0) (r:11+ d*11≠0) (j:p4 (Bm+(aq 1 3 1 3 a)+(aq 1 2 1 3 b))=65) (i:p4 (Bm+(aq 1 3 1 3 a)+(aq 0 3 1 3 c))=65) (k:p4 (Bm+(aq 1 3 1 3 a)+(aq 0 2 1 3 d))=65) (n:p4 (Bm+(aq 1 2 1 3 b)+(aq 0 3 1 3 c))=65) (l:p4 (Bm+(aq 1 2 1 3 b)+(aq 0 2 1 3 d))=65) (m:p4 (Bm+(aq 0 3 1 3 c)+(aq 0 2 1 3 d))=65),False):=by
 refine⟨?_,?_,?_,?_⟩<;>intro a b c d v e q t f p u g o s h r j i k n l m;all_goals
  simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at j i k n l m
  grind
def ak7 (a b c d:ℂ) (w:a≠0) (l:a*11-11≠0) (r:11+ a*16≠0) (u:b≠0) (m:b*11-11≠0) (q:11+ b*16≠0) (v:c≠0) (n:c*11-11≠0) (p:16+ c*11≠0) (t:d≠0) (o:d*11-11≠0) (s:16+ d*11≠0)
  (f:p4 (Bm+(aq 1 3 0 1 a)+(aq 1 2 0 1 b))=65)
  (e:p4 (Bm+(aq 1 3 0 1 a)+(aq 0 3 0 1 c))=65)
  (g:p4 (Bm+(aq 1 3 0 1 a)+(aq 0 2 0 1 d))=65)
  (j:p4 (Bm+(aq 1 2 0 1 b)+(aq 0 3 0 1 c))=65)
  (h:p4 (Bm+(aq 1 2 0 1 b)+(aq 0 2 0 1 d))=65)
  (i:p4 (Bm+(aq 0 3 0 1 c)+(aq 0 2 0 1 d))=65)
  (r0:(aq 1 3 0 1 a) (1,0)*(aq 1 2 0 1 b) (1,1)=(aq 1 3 0 1 a) (1,1)*(aq 1 2 0 1 b) (1,0))
  (k:(aq 0 3 0 1 c) (0,0)*(aq 0 2 0 1 d) (0,1)=(aq 0 3 0 1 c) (0,1)*(aq 0 2 0 1 d) (0,0)):False:=by
 simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at f e g j h i r0 k;grind
def alb (a b c d:ℂ) (z:a≠0) (q:a*11-11≠0) (i:11+ a*16≠0) (x:b≠0) (r:b*11-11≠0) (g:11+ b*16≠0) (y:c≠0) (s:c*11-11≠0) (f:16+ c*11≠0) (u:d≠0) (t:d*11-11≠0) (j:16+ d*11≠0)
  (Jo:p4 (Bm+(aq 1 3 0 1 a)+(aq 1 2 0 1 b))=65)
  (e:p4 (Bm+(aq 1 3 0 1 a)+(aq 0 3 0 1 c))=65)
  (k:p4 (Bm+(aq 1 3 0 1 a)+(aq 0 2 0 1 d))=65)
  (o:p4 (Bm+(aq 1 2 0 1 b)+(aq 0 3 0 1 c))=65)
  (l:p4 (Bm+(aq 1 2 0 1 b)+(aq 0 2 0 1 d))=65)
  (m:p4 (Bm+(aq 0 3 0 1 c)+(aq 0 2 0 1 d))=65)
  (r0:(aq 1 3 0 1 a) (3,0)*(aq 0 3 0 1 c) (3,1)=(aq 1 3 0 1 a) (3,1)*(aq 0 3 0 1 c) (3,0))
  (p:(aq 1 2 0 1 b) (2,0)*(aq 0 2 0 1 d) (2,1)=(aq 1 2 0 1 b) (2,1)*(aq 0 2 0 1 d) (2,0)):False:=by
 simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at Jo e k o l m r0 p
 have v:a=c:=by
  have h:(a- c)*((11+ a*16)*(16+ c*11))=0:=by grind
  have n:=(A0.1 h).resolve_right (mul_ne_zero i f);grind
 have w:b=d:=by
  have h:(b- d)*((11+ b*16)*(16+ d*11))=0:=by grind
  have n:=(A0.1 h).resolve_right (mul_ne_zero g j);grind
 grind
def ak9 (a b c d:ℂ) (v:a≠0) (k:a*11-11≠0) (q:11+ a*11≠0) (t:b≠0) (l:b*11-11≠0) (p:11+ b*16≠0) (u:c≠0) (m:c*11-11≠0) (o:16+ c*11≠0) (s:d≠0) (n:d*16-11≠0) (r:16+ d*11≠0)
  (f:p4 (Bm+(aq 2 3 0 1 a)+(aq 1 2 0 1 b))=65)
  (e:p4 (Bm+(aq 2 3 0 1 a)+(aq 0 3 0 1 c))=65)
  (g:p4 (Bm+(aq 2 3 0 1 a)+(aq 0 1 0 1 d))=65)
  (j:p4 (Bm+(aq 1 2 0 1 b)+(aq 0 3 0 1 c))=65)
  (h:p4 (Bm+(aq 1 2 0 1 b)+(aq 0 1 0 1 d))=65)
  (i:p4 (Bm+(aq 0 3 0 1 c)+(aq 0 1 0 1 d))=65):False:=by
 simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at f e g j h i;grind
def ak8 (a b c d:ℂ) (w:a≠0) (l:a*16-11≠0) (r:11+ a*11≠0) (u:b≠0) (m:b*11-16≠0) (q:11+ b*11≠0) (v:c≠0) (n:c*16-11≠0) (p:11+ c*11≠0) (t:d≠0) (o:d*11-16≠0) (s:11+ d*11≠0)
  (f:p4 (Bm+(aq 1 3 2 3 a)+(aq 1 2 2 3 b))=65)
  (e:p4 (Bm+(aq 1 3 2 3 a)+(aq 0 3 2 3 c))=65)
  (g:p4 (Bm+(aq 1 3 2 3 a)+(aq 0 2 2 3 d))=65)
  (j:p4 (Bm+(aq 1 2 2 3 b)+(aq 0 3 2 3 c))=65)
  (h:p4 (Bm+(aq 1 2 2 3 b)+(aq 0 2 2 3 d))=65)
  (i:p4 (Bm+(aq 0 3 2 3 c)+(aq 0 2 2 3 d))=65)
  (r0:(aq 1 3 2 3 a) (1,2)*(aq 1 2 2 3 b) (1,3)=(aq 1 3 2 3 a) (1,3)*(aq 1 2 2 3 b) (1,2))
  (k:(aq 0 3 2 3 c) (0,2)*(aq 0 2 2 3 d) (0,3)=(aq 0 3 2 3 c) (0,3)*(aq 0 2 2 3 d) (0,2)):False:=by
 simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at f e g j h i r0 k;grind
def alc (a b c d:ℂ) (z:a≠0) (q:a*16-11≠0) (i:11+ a*11≠0) (x:b≠0) (r:b*11-16≠0) (g:11+ b*11≠0) (y:c≠0) (s:c*16-11≠0) (f:11+ c*11≠0) (u:d≠0) (t:d*11-16≠0) (j:11+ d*11≠0)
  (Jo:p4 (Bm+(aq 1 3 2 3 a)+(aq 1 2 2 3 b))=65)
  (e:p4 (Bm+(aq 1 3 2 3 a)+(aq 0 3 2 3 c))=65)
  (k:p4 (Bm+(aq 1 3 2 3 a)+(aq 0 2 2 3 d))=65)
  (o:p4 (Bm+(aq 1 2 2 3 b)+(aq 0 3 2 3 c))=65)
  (l:p4 (Bm+(aq 1 2 2 3 b)+(aq 0 2 2 3 d))=65)
  (m:p4 (Bm+(aq 0 3 2 3 c)+(aq 0 2 2 3 d))=65)
  (r0:(aq 1 3 2 3 a) (3,2)*(aq 0 3 2 3 c) (3,3)=(aq 1 3 2 3 a) (3,3)*(aq 0 3 2 3 c) (3,2))
  (p:(aq 1 2 2 3 b) (2,2)*(aq 0 2 2 3 d) (2,3)=(aq 1 2 2 3 b) (2,3)*(aq 0 2 2 3 d) (2,2)):False:=by
 simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at Jo e k o l m r0 p
 have v:a=c:=by
  have h:(a- c)*((11+ a*11)*(11+ c*11))=0:=by grind
  have n:=(A0.1 h).resolve_right (mul_ne_zero i f);grind
 have w:b=d:=by
  have h:(b- d)*((11+ b*11)*(11+ d*11))=0:=by grind
  have n:=(A0.1 h).resolve_right (mul_ne_zero g j);grind
 grind
def ala (a b c d:ℂ) (v:a≠0) (k:a*16-11≠0) (q:16+ a*11≠0) (t:b≠0) (l:b*11-16≠0) (p:11+ b*11≠0) (u:c≠0) (m:c*16-11≠0) (o:11+ c*11≠0) (s:d≠0) (n:d*11-11≠0) (r:11+ d*11≠0)
  (f:p4 (Bm+(aq 2 3 2 3 a)+(aq 1 2 2 3 b))=65)
  (e:p4 (Bm+(aq 2 3 2 3 a)+(aq 0 3 2 3 c))=65)
  (g:p4 (Bm+(aq 2 3 2 3 a)+(aq 0 1 2 3 d))=65)
  (j:p4 (Bm+(aq 1 2 2 3 b)+(aq 0 3 2 3 c))=65)
  (h:p4 (Bm+(aq 1 2 2 3 b)+(aq 0 1 2 3 d))=65)
  (i:p4 (Bm+(aq 0 3 2 3 c)+(aq 0 1 2 3 d))=65):False:=by
 simp +decide only[p4,aq,MU,E,Bm,A1,A4,A5,A9,A8]at f e g j h i;grind
def T3F (c:Fq) (Z:Mt) (a b d:ℂ): Prop :=
 MU 1 c+ a*MU 3 c=0/\MU 1 c+ b*MU 2 c=0/\MU 0 c+ d*MU 3 c=0/\
 (∀ s:ℂ,p4 (Bm+ s•Z)=65)/\(∀ s:ℂ,p4 (Bm+ s•Z+ M4 1 3 c a)=65)/\
 (∀ s:ℂ,p4 (Bm+ s•Z+ M4 1 2 c b)=65)/\(∀ s:ℂ,p4 (Bm+ s•Z+ M4 0 3 c d)=65)
def WO:(∀ (Z:Mt) (a b c:ℂ) (d:∀ i,Z (i,0)=0) (e:∀ i,Z (i,1)=0) (hp:Z (0,2)=1\/Z (1,2)=1\/Z (2,2)=1\/Z (3,2)=1\/Z (0,3)=1\/Z (1,3)=1\/Z (2,3)=1\/Z (3,3)=1) (H:T3F 0 Z a b c),False)/\(∀ (Z:Mt) (a b c:ℂ) (d:∀ i,Z (i,1)=0) (e:∀ i,Z (i,2)=0) (hp:Z (0,0)=1\/Z (1,0)=1\/Z (2,0)=1\/Z (3,0)=1\/Z (0,3)=1\/Z (1,3)=1\/Z (2,3)=1\/Z (3,3)=1) (H:T3F 1 Z a b c),False)/\(∀ (Z:Mt) (a b c:ℂ) (d:∀ i,Z (i,2)=0) (e:∀ i,Z (i,3)=0) (hp:Z (0,0)=1\/Z (1,0)=1\/Z (2,0)=1\/Z (3,0)=1\/Z (0,1)=1\/Z (1,1)=1\/Z (2,1)=1\/Z (3,1)=1) (H:T3F 2 Z a b c),False)/\(∀ (Z:Mt) (a b c:ℂ) (d:∀ i,Z (i,3)=0) (e:∀ i,Z (i,0)=0) (hp:Z (0,1)=1\/Z (1,1)=1\/Z (2,1)=1\/Z (3,1)=1\/Z (0,2)=1\/Z (1,2)=1\/Z (2,2)=1\/Z (3,2)=1) (H:T3F 3 Z a b c),False):=by
 refine⟨?_,?_,?_,?_⟩<;>intro Z a b c d e hp H;all_goals
  obtain⟨k,l,m,f,g,h,j⟩:=H
  have w:=f 1;have x:=f 2;have y:=f 3;have z:=f 4
  have n:=g 1;have o:=g 2;have p:=g 3
  have q:=h 1;have r:=h 2;have s:=h 3
  have t:=j 1;have u:=j 2;have v:=j 3
  clear f g h j
  simp +decide only[MU,p4,M4,E,Bm,A1,A4,A5,A9,
   A8,d,e]at k l m w x y z n o p q r s t u v
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp<;>grind
lemma afS (t u c:Fq) (y:ℂ):NV (M4 t u c y)=MU t c+ y*MU u c:=by
 simp only[M4,ZU,R7,aep]
def WM (L:Sq) (i:∀ t∈L,p4 (Bm+ t)=65) (t u c:Fq) (f:t≠u)
  (g:Mt) (b:g∈L) (j:Mc t u c g):∃ y:ℂ,MU t c+ y*MU u c=0/\M4 t u c y∈L:=by
 obtain⟨e,y,d,-,rfl⟩:=VC t u c f g j
 have a:NV (e•M4 t u c y)=0:=QC _ (λs=> i _ (L.smul_mem s b))
 rw[R7,afS]at a;refine⟨y,(A0.1 a).resolve_left d,?_⟩;have h:=L.smul_mem e⁻¹ b;rwa[H0,G5 d,G1]at h
def ME (L:Sq) (k:∀ t∈L,p4 (Bm+ t)=65) (t u c d:Fq) (i:t≠u)
  (h:c≠d) (g:Mt) (hg:g∈L) (m:Ke t u c d g):
  ∃ a q:ℂ,a≠0/\q≠0/\q*MU u d- MU u c≠0/\MU t c+ q*MU t d≠0/\
   g=a•aq t u c d q/\aq t u c d q∈L:=by
 obtain⟨a,q,f,n,l,b,e⟩:=
  O9 t u c d i h g m (QC g (λs=> k _ (L.smul_mem s hg)))
 refine⟨a,q,f,n,l,b,e,?_⟩;have j:=L.smul_mem a⁻¹ hg;rwa[e,H0,G5 f,G1]at j
def Uc (L:Sq) (f:∀ t∈L,p4 (Bm+ t)=65) (e:finrank ℂ L=6) (c d:Fq)
  (a:c≠d):∃ Y∈L,Y≠0/\(∀ i,Y (i,c)=0)/\(∀ i,Y (i,d)=0):=by
 obtain⟨X,g,b,j,k⟩:=Zv (L.map Mv) (QR L f) (by rw[Qv];exact e) c d a
 obtain⟨Y,hY,rfl⟩:=B6.1 g
 exact⟨Y,hY,λh=> b (by rw[h,H5]),λi=> by simpa[Mw] using j i,
  λi=> by simpa[Mw] using k i⟩
def Pn (L:Sq) (c d e f:Fq) (Mr:∀ j:Fq,j=c\/j=d\/j=e\/j=f)
  (Y:Mt) (m:Y∈L) (l:Y≠0) (hc:∀ i,Y (i,c)=0) (g:∀ i,Y (i,d)=0):
  ∃ Z∈L,(∀ i,Z (i,c)=0)/\(∀ i,Z (i,d)=0)/\
   (Z (0,e)=1\/Z (1,e)=1\/Z (2,e)=1\/Z (3,e)=1\/Z (0,f)=1\/Z (1,f)=1\/
    Z (2,f)=1\/Z (3,f)=1):=by
 have h:∃ p:Fq× Fq,(p.2=e\/p.2=f)/\Y p≠0:=by
  by_contra b;apply l;funext ⟨i,j⟩;rcases Mr j with rfl | rfl | rfl | rfl
  .exact hc i
  .exact g i
  .by_contra od;exact b ⟨(i,j),Or.inl rfl,od⟩
  .by_contra od;exact b ⟨(i,j),Or.inr rfl,od⟩
 obtain⟨⟨i,j⟩,n,o⟩:=h
 refine⟨(Y (i,j))⁻¹•Y,L.smul_mem _ m,λk=> by simp[hc k],λk=> by simp[g k],?_⟩
 have a:((Y (i,j))⁻¹•Y) (i,j)=1:=by simp[o]
 rcases n with rfl | rfl
 .fin_cases i
  .exact Or.inl a
  .exact Or.inr (Or.inl a)
  .exact Or.inr (Or.inr (Or.inl a))
  .exact Or.inr (Or.inr (Or.inr (Or.inl a)))
 .fin_cases i
  .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a))))
  .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a)))))
  .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a))))))
  .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr a))))))
def abR (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65) (m:finrank ℂ L=6):aaQ L:=by
 intro c u KQ r y z n o p q
 obtain⟨j,v,A⟩:=WM L b 1 3 c (by decide) u y o
 obtain⟨k,w,B⟩:=WM L b 1 2 c (by decide) KQ z p
 obtain⟨l,x,C⟩:=WM L b 0 3 c (by decide) r n q
 have F:∀ Z∈L,T3F c Z j k l:=λZ a=>
  ⟨v,w,x,λs=> b _ (L.smul_mem s a),
   λs=> by rw[D1];exact b _ (L.add_mem (L.smul_mem s a) A),
   λs=> by rw[D1];exact b _ (L.add_mem (L.smul_mem s a) B),
   λs=> by rw[D1];exact b _ (L.add_mem (L.smul_mem s a) C)⟩
 fin_cases c
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b m 0 1 (by decide)
  obtain⟨Z,a,g,h,i⟩:=Pn L 0 1 2 3 (by decide) Y d h0 e f
  exact WO.1 Z j k l g h i (F Z a)
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b m 1 2 (by decide)
  obtain⟨Z,a,g,h,i⟩:=Pn L 1 2 0 3 (by decide) Y d h0 e f
  exact WO.2.1 Z j k l g h i (F Z a)
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b m 2 3 (by decide)
  obtain⟨Z,a,g,h,i⟩:=Pn L 2 3 0 1 (by decide) Y d h0 e f
  exact WO.2.2.1 Z j k l g h i (F Z a)
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b m 3 0 (by decide)
  obtain⟨Z,a,g,h,i⟩:=Pn L 3 0 1 2 (by decide) Y d h0 e f
  exact WO.2.2.2 Z j k l g h i (F Z a)
def abG (k a:ℂ) (f:k≠0) (d:a≠0) (x1 x2 b c:ℂ)
  (h:k*x1*(a*c)=k*x2*(a*b)):x1*c=x2*b:=by
 have e:(k*a)*(x1*c- x2*b)=0:=by grind
 have g:=(A0.1 e).resolve_left (mul_ne_zero f d);grind
def abQ (L:Sq) (p:∀ t∈L,p4 (Bm+ t)=65):aaP L:=by
 intro c d Kx Ks KQ as au ZS ZT ao ap ai aj al am ae ag;have O:c≠d:=D5 Kx
 obtain⟨k1,u,Q,gq,na1,q,V,m1⟩:=ME L p 1 3 c d (by decide) O Ks ZS ai
 obtain⟨k2,n,N,l,f,Ij,W,m2⟩:=ME L p 1 2 c d (by decide) O KQ ZT aj
 obtain⟨k3,o,S,m,g,j,e3,o7⟩:=ME L p 0 3 c d (by decide) O as ao al
 obtain⟨k4,v,y,NH,i,r,e4,e⟩:=ME L p 0 2 c d (by decide) O au ap am
 have P:∀ X Y:Mt,X∈L->Y∈L->p4 (Bm+ X+ Y)=65:=
  λX Y hX hY=> by rw[D1];exact p _ (L.add_mem hX hY)
 have R:∀ (X Y:Mt) (k Z:ℂ) (T U:Mt) (s M:Fq) (a b:Fq),k≠0->Z≠0->X=k•T->Y=Z•U->
   X (s,a)*Y (M,b)=X (s,b)*Y (M,a)->T (s,a)*U (M,b)=T (s,b)*U (M,a):=by
  intro X Y k Z T U s M a b hk SY hX hY h;rw[hX,hY]at h
  exact abG k Z hk SY _ _ _ _ (by simpa only[A4,A5] using h)
 fin_cases c<;>fin_cases d<;>(try exact absurd Kx (by decide))
 .rcases ae with⟨P1,P2⟩ | ⟨Nx,B,z⟩
  .exact ak7 u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
    (R _ _ _ _ _ _ 1 1 0 1 Q N V W (P1 0 1)) (R _ _ _ _ _ _ 0 0 0 1 S y e3 e4 (P2 0 1))
  .rcases ag with⟨P3,P4⟩ | ⟨D,C,A⟩
   .exact alb u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
     (R _ _ _ _ _ _ 3 3 0 1 Q S V e3 (P3 0 1)) (R _ _ _ _ _ _ 2 2 0 1 N y W e4 (P4 0 1))
   .obtain⟨k5,q5,av,J,E,G,-,w⟩:=ME L p 2 3 0 1 (by decide) (by decide) Nx B z
    obtain⟨k6,q6,aw,K,F,H,-,x⟩:=ME L p 0 1 0 1 (by decide) (by decide) D C A
    exact ak9 q5 n o q6 J E G l f Ij m g j K F H
     (P _ _ w m2) (P _ _ w o7) (P _ _ w x) (P _ _ m2 o7) (P _ _ m2 x) (P _ _ o7 x)
 .exact WR.1 u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
 .exact WR.2.1 u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
 .exact WR.2.2.1 u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
 .exact WR.2.2.2 u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
 .rcases ae with⟨P1,P2⟩ | ⟨Nx,B,z⟩
  .exact ak8 u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
    (R _ _ _ _ _ _ 1 1 2 3 Q N V W (P1 2 3)) (R _ _ _ _ _ _ 0 0 2 3 S y e3 e4 (P2 2 3))
  .rcases ag with⟨P3,P4⟩ | ⟨D,C,A⟩
   .exact alc u n o v gq na1 q l f Ij m g j NH i r (P _ _ m1 m2) (P _ _ m1 o7) (P _ _ m1 e) (P _ _ m2 o7) (P _ _ m2 e) (P _ _ o7 e)
     (R _ _ _ _ _ _ 3 3 2 3 Q S V e3 (P3 2 3)) (R _ _ _ _ _ _ 2 2 2 3 N y W e4 (P4 2 3))
   .obtain⟨k5,q5,av,J,E,G,-,w⟩:=ME L p 2 3 2 3 (by decide) (by decide) Nx B z
    obtain⟨k6,q6,aw,K,F,H,-,x⟩:=ME L p 0 1 2 3 (by decide) (by decide) D C A
    exact ala q5 n o q6 J E G l f Ij m g j K F H
     (P _ _ w m2) (P _ _ w o7) (P _ _ w x) (P _ _ m2 o7) (P _ _ m2 x) (P _ _ o7 x)
def abO (c:∀ i:Fin 186,ak (rA i) (rB i) (rC i))
  (L:Sq) (a:∀ t∈L,p4 (Bm+ t)=65) (b:finrank ℂ L=6)
  (e:∀ r,finrank ℂ (L.map (af r))=3) (d:UK L):False:=
 SR0 c (λL a b=> abR L a b) (λL a _=> abQ L a) L a b e d
def Kq (L:Sq) (u:Fq): Prop := ∃ X∈L,X≠0/\ ∀ i j,i≠u->X (i,j)=0
def agV (L:Sq) (h:∀ u,¬ Kq L u):UK L:=by
 intro u X c a;by_contra b;exact h u ⟨X,c,b,a⟩
def YC (L:Sq) (a:Equiv.Perm Fq) (u:Fq) (h:Kq L u):
  Kq (L.map (gp a)) (a u):=by
 obtain⟨X,d,c,f⟩:=h
 refine⟨gp a X,C4 d,λb=> c (O5 a (by rw[b,H5])),
  λi j e=> ?_⟩
 rw[my];apply f;intro b;apply e;rw[<- b];simp
lemma Zw (L:Sq) (a:Equiv.Perm Fq):
  (L.map (gp a)).map (gp a.symm)=L:=by
 rw[<- H8]
 have e:(gp a.symm).comp (gp a)=LinearMap.id:=by
  apply LinearMap.ext;intro X;funext ⟨i,j⟩;simp[my]
 rw[e,Submodule.map_id]
def ou (L:Sq) (a:Equiv.Perm Fq) (u v:Fq) (h:a u=v) (s:Kq L u):
  Kq (L.map (gp a)) v:=by
 rw[<- h];exact YC L a u s
def mo (L:Sq) (a:Equiv.Perm Fq) (u v:Fq) (h:a u=v) (s:¬ Kq L u):
  ¬ Kq (L.map (gp a)) v:=by
 intro b;apply s;have c:=YC _ a.symm _ b;rwa[Zw,<- h,Equiv.symm_apply_apply]at c
def W5: Prop := ∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6->
 (∀ r,finrank ℂ (L.map (af r))=3)->Kq L 0-> ¬ Kq L 1-> ¬ Kq L 2-> ¬ Kq L 3->False
def RE: Prop := ∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6->
 (∀ r,finrank ℂ (L.map (af r))=3)->Kq L 0->Kq L 1-> ¬ Kq L 2-> ¬ Kq L 3->False
def W6: Prop := ∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6->
 (∀ r,finrank ℂ (L.map (af r))=3)->Kq L 1->Kq L 2->Kq L 3->False
def Xy (l:∀ i:Fin 186,ak (rA i) (rB i) (rC i)) (k:W5) (e:RE) (j:W6)
  (L:Sq) (h:∀ t∈L,p4 (Bm+ t)=65) (f:finrank ℂ L=6)
  (g:∀ r,finrank ℂ (L.map (af r))=3):False:=by
 have T:∀ σ:Equiv.Perm (Fq),(∀ t∈L.map (gp σ),p4 (Bm+ t)=65)/\
   finrank ℂ (L.map (gp σ))=6/\(∀ r,finrank ℂ ((L.map (gp σ)).map (af r))=3):=
  λσ=>⟨LY L h σ,by rw[o6];exact f,Pg L σ g⟩
 by_cases d:Kq L 0<;>by_cases a:Kq L 1<;>by_cases b:Kq L 2<;>by_cases c:Kq L 3
 .exact j L h f g a b c
 .exact j _ (T (swap 0 3)).1 (T _).2.1 (T _).2.2 (ou L _ 1 1 (by decide) a)
   (ou L _ 2 2 (by decide) b) (ou L _ 0 3 (by decide) d)
 .exact j _ (T (swap 0 2)).1 (T _).2.1 (T _).2.2 (ou L _ 1 1 (by decide) a)
   (ou L _ 0 2 (by decide) d) (ou L _ 3 3 (by decide) c)
 .exact e L h f g d a b c
 .exact j _ (T (swap 0 1)).1 (T _).2.1 (T _).2.2 (ou L _ 0 1 (by decide) d)
   (ou L _ 2 2 (by decide) b) (ou L _ 3 3 (by decide) c)
 .exact e _ (T (swap 1 2)).1 (T _).2.1 (T _).2.2 (ou L _ 0 0 (by decide) d)
   (ou L _ 2 1 (by decide) b) (mo L _ 1 2 (by decide) a) (mo L _ 3 3 (by decide) c)
 .exact e _ (T (swap 1 3)).1 (T _).2.1 (T _).2.2 (ou L _ 0 0 (by decide) d)
   (ou L _ 3 1 (by decide) c) (mo L _ 2 2 (by decide) b) (mo L _ 1 3 (by decide) a)
 .exact k L h f g d a b c
 .exact j L h f g a b c
 .exact e _ (T (swap 0 2)).1 (T _).2.1 (T _).2.2 (ou L _ 2 0 (by decide) b)
   (ou L _ 1 1 (by decide) a) (mo L _ 0 2 (by decide) d) (mo L _ 3 3 (by decide) c)
 .exact e _ (T (swap 0 3)).1 (T _).2.1 (T _).2.2 (ou L _ 3 0 (by decide) c)
   (ou L _ 1 1 (by decide) a) (mo L _ 2 2 (by decide) b) (mo L _ 0 3 (by decide) d)
 .exact k _ (T (swap 0 1)).1 (T _).2.1 (T _).2.2 (ou L _ 1 0 (by decide) a)
   (mo L _ 0 1 (by decide) d) (mo L _ 2 2 (by decide) b) (mo L _ 3 3 (by decide) c)
 .exact e _ (T (swap 0 2*swap 1 3)).1 (T _).2.1 (T _).2.2 (ou L _ 2 0 (by decide) b)
   (ou L _ 3 1 (by decide) c) (mo L _ 0 2 (by decide) d) (mo L _ 1 3 (by decide) a)
 .exact k _ (T (swap 0 2)).1 (T _).2.1 (T _).2.2 (ou L _ 2 0 (by decide) b)
   (mo L _ 1 1 (by decide) a) (mo L _ 0 2 (by decide) d) (mo L _ 3 3 (by decide) c)
 .exact k _ (T (swap 0 3)).1 (T _).2.1 (T _).2.2 (ou L _ 3 0 (by decide) c)
   (mo L _ 1 1 (by decide) a) (mo L _ 2 2 (by decide) b) (mo L _ 0 3 (by decide) d)
 .exact abO l L h f g (agV L (λu=> by fin_cases u<;>assumption))
def Q7: Prop := ∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6->
 (∃ r,finrank ℂ (L.map (af r))≤2)->(∃ c,finrank ℂ ((L.map Mv).map (af c))≤2)->False
def QV (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65) (r:Fq):
  finrank ℂ (L.map (af r))≤3:=by
 have a:=LZ L b r;have c:=H4 (L.map (af r))
 have d:finrank ℂ (Fq->ℂ)=4:=by simp
 by_contra h;apply a;apply M1;omega
def Xo (e:∀ i:Fin 186,ak (rA i) (rB i) (rC i)) (f:W5) (g:RE)
  (h:W6) (k:Q7):
  ¬ (∃ L:Submodule ℂ (Fq× Fq->ℂ),finrank ℂ L=6/\ ∀ t∈L,
   permanent (Matrix.of λ(i j:Fq)=>(if i=j then (2:ℂ) else 1)+ t (i,j))=65):=by
 rintro⟨L,h6,hL0⟩
 have b:∀ t∈L,p4 (Bm+ t)=65:=λt l=> by rw[<- ago];exact hL0 t l
 by_cases d:∀ r,finrank ℂ (L.map (af r))=3
 .exact Xy e f g h L b h6 d
 .by_cases a:∀ c,finrank ℂ ((L.map Mv).map (af c))=3
  .exact Xy e f g h (L.map Mv) (QR L b) (by rw[Qv];exact h6) a
  .push_neg at d a;obtain⟨r,n⟩:=d;obtain⟨c,m⟩:=a
   exact k L b h6 ⟨r,by have :=QV L b r;omega⟩
    ⟨c,by have :=QV (L.map Mv) (QR L b) c;omega⟩
lemma z3 (x y z:ℂ) (h:x*y*z=0):x=0\/y=0\/z=0:=by
 rcases A0.1 h with h | h
 .rcases A0.1 h with h | h
  .exact Or.inl h
  .exact Or.inr (Or.inl h)
 .exact Or.inr (Or.inr h)
def aek (g q n i j k s l m o r p:ℂ)
  (z:11*g+16*q+11*n+11*i=0)
  (A:11*j+11*k+16*s+11*l=0)
  (B:11*m+11*o+11*r+16*p=0)
  (y:3*g*k+3*g*s+2*g*l+3*q*j+5*q*s+3*q*l+3*n*j+5*n*k+3*n*l+2*i*j+3*i*k+3*i*s=0)
  (x:3*g*o+2*g*r+3*g*p+3*q*m+3*q*r+5*q*p+2*n*m+3*n*o+3*n*p+3*i*m+5*i*o+3*i*r=0)
  (C:2*j*o+3*j*r+3*j*p+2*k*m+3*k*r+3*k*p+3*s*m+3*s*o+5*s*p+3*l*m+3*l*o+5*l*r=0)
  (D:q*s*p+ q*l*r+ n*k*p+ n*l*o+ i*k*r+ i*s*o=0)
  (E:g*s*p+ g*l*r+ n*j*p+ n*l*m+ i*j*r+ i*s*m=0)
  (F:g*k*p+ g*l*o+ q*j*p+ q*l*m+ i*j*o+ i*k*m=0)
  (G:g*k*r+ g*s*o+ q*j*r+ q*s*m+ n*j*o+ n*k*m=0)
  (c:g*j*m=0\/q*k*o=0)
  (d:g*j*m=0\/n*s*r=0)
  (e:g*j*m=0\/i*l*p=0)
  (f:q*k*o=0\/n*s*r=0)
  (a:q*k*o=0\/i*l*p=0)
  (b:n*s*r=0\/i*l*p=0)
  (u:g=1\/g=0/\n=1\/g=0/\n=0/\i=1)
  (v:j=1\/j=0/\k=1\/j=0/\k=0/\l=1)
  (w:m=1\/m=0/\o=1\/m=0/\o=0/\r=1):False:=by
 rcases u with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩<;>rcases v with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩<;>
  rcases w with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
 .rcases z3 _ _ _ (c.resolve_left (by norm_num)) with rfl | rfl | rfl<;>
   rcases z3 _ _ _ (d.resolve_left (by norm_num)) with rfl | rfl | rfl<;>
   rcases z3 _ _ _ (e.resolve_left (by norm_num)) with rfl | rfl | rfl<;>
   (clear c d e f a b;grind)
 .by_cases t:q*k*1=0
  .rcases z3 _ _ _ t with rfl | rfl | h<;>(clear c d e f a b;grind)
  .rcases z3 _ _ _ (f.resolve_left t) with rfl | rfl | rfl<;>
    rcases z3 _ _ _ (a.resolve_left t) with rfl | rfl | rfl<;>
    (clear c d e f a b;grind)
 .clear c d e f a b;grind
 .by_cases t:i*l*p=0
  .rcases z3 _ _ _ t with rfl | rfl | rfl<;>(clear c d e f a b;grind)
  .rcases z3 _ _ _ (a.resolve_right t) with rfl | h | rfl<;>
    rcases z3 _ _ _ (b.resolve_right t) with rfl | rfl | rfl<;>
    (clear c d e f a b;grind)
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .by_cases t:i*l*p=0
  .rcases z3 _ _ _ t with rfl | rfl | rfl<;>(clear c d e f a b;grind)
  .rcases z3 _ _ _ (a.resolve_right t) with rfl | rfl | rfl<;>
    rcases z3 _ _ _ (b.resolve_right t) with h | rfl | rfl<;>
    (clear c d e f a b;grind)
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
 .clear c d e f a b;grind
lemma Ml (L:Sq) (j:Fq) (Y:Mt) (a:Y∈L):
  (λi=> Y (i,j))∈(L.map Mv).map (af j):=
 B6.2 ⟨Mv Y,C4 a,by ext i;rfl⟩
lemma NM (u j:Fq) (Y:Mt) (b:∀ i k,i≠u->Y (i,k)=0):
  (λi=> Y (i,j))=Y (u,j)•(single u (1:ℂ):Fq->ℂ):=by
 ext i;by_cases a:i=u
 .subst a;simp
 .simp[a,b i j a]
def YL (L:Sq) (r:∀ t∈L,p4 (Bm+ t)=65) (j:Fq) (a b c:Mt)
  (o:a∈L) (p:b∈L) (q:c∈L) (x:∀ i k,i≠1->a (i,k)=0)
  (y:∀ i k,i≠2->b (i,k)=0) (z:∀ i k,i≠3->c (i,k)=0)
  (u:a (1,j)≠0) (v:b (2,j)≠0) (w:c (3,j)≠0):∀ X∈L,X (0,j)=0:=by
 intro X s;by_contra hx;apply LZ (L.map Mv) (QR L r) j;have d:=Ml L j a o;rw[NM 1 j a x]at d;have e:=Ml L j b p;rw[NM 2 j b y]at e;have f:=Ml L j c q;rw[NM 3 j c z]at f;have g:=Ir _ _ _ u d;have h:=Ir _ _ _ v e;have l:=Ir _ _ _ w f;have m:=Ml L j X s
 have hv:X (0,j)•(single 0 (1:ℂ):Fq->ℂ)=(λi=> X (i,j))- X (1,j)•single 1 (1:ℂ)
   - X (2,j)•single 2 (1:ℂ)- X (3,j)•single 3 (1:ℂ):=by
  ext i;fin_cases i<;>simp[]
 have n:(single 0 (1:ℂ):Fq->ℂ)∈(L.map Mv).map (af j):=by
  apply Ir _ _ _ hx;rw[hv];exact F8 _ (F8 _ (F8 _ m (D6 _ _ g))
   (D6 _ _ h)) (D6 _ _ l)
 apply M5;intro k;fin_cases k
 .exact n
 .exact g
 .exact h
 .exact l
def af9 (L:Sq) (hp:finrank ℂ (L.map (af 0))=3) (j k:Fq) (f:j≠k)
  (g:∀ X∈L,X (0,j)=0) (i:∀ X∈L,X (0,k)=0):False:=by
 have c:∀ w∈L.map (af 0),w j=0:=by
  intro w b;obtain⟨X,a,rfl⟩:=B6.1 b;exact g X a
 have d:∀ w∈L.map (af 0),w k=0:=by
  intro w b;obtain⟨X,a,rfl⟩:=B6.1 b;exact i X a
 have n:(single j (1:ℂ):Fq->ℂ)∉ L.map (af 0):=λh=> by
  have :=c _ h;simp at this
 have o:(single k (1:ℂ):Fq->ℂ)∉
   L.map (af 0) ⊔ span ℂ {(single j (1:ℂ):Fq->ℂ)}:=by
  intro h;obtain⟨y,l,z,m,e⟩:=C5.1 h;obtain⟨t,rfl⟩:=C6.1 m;have :=congrFun e k;simp[Ne.symm f,d y l]at this
 have p:=du _ _ n;have q:=du _ _ o;have r:=H4 (L.map (af 0) ⊔ span ℂ {(single j (1:ℂ):Fq->ℂ)} ⊔
  span ℂ {(single k (1:ℂ):Fq->ℂ)})
 have s:finrank ℂ (Fq->ℂ)=4:=by simp
 omega
def ans (L:Sq) (hL:∀ t∈L,p4 (Bm+ t)=65) (p:finrank ℂ (L.map (af 0))=3)
  (Y1 c d:Mt) (e:Y1∈L) (f:c∈L) (g:d∈L) (l:∀ i k,i≠1->Y1 (i,k)=0)
  (m:∀ i k,i≠2->c (i,k)=0) (n:∀ i k,i≠3->d (i,k)=0) (j k:Fq) (o:j≠k):
  Y1 (1,j)*c (2,j)*d (3,j)=0\/Y1 (1,k)*c (2,k)*d (3,k)=0:=by
 by_contra h;push_neg at h;obtain⟨a,b⟩:=h;exact af9 L p j k o
  (YL L hL j Y1 c d e f g l m n (D2 (D2 a))
   (F9 (D2 a)) (F9 a))
  (YL L hL k Y1 c d e f g l m n (D2 (D2 b))
   (F9 (D2 b)) (F9 b))
def VU (L:Sq) (u e f g:Fq) (X:Mt) (d:X∈L) (n:X≠0)
  (l:∀ i j,i≠u->X (i,j)=0) (m:∀ j,j=u\/j=e\/j=f\/j=g)
  (o:X (u,e)=0->X (u,f)=0->X (u,g)=0->X (u,u)=0):
  ∃ Y∈L,(∀ i j,i≠u->Y (i,j)=0)/\
   (Y (u,e)=1\/Y (u,e)=0/\Y (u,f)=1\/Y (u,e)=0/\Y (u,f)=0/\Y (u,g)=1):=by
 have k:∀ x:ℂ,∀ i j,i≠u->(x•X) (i,j)=0:=λx i j c=> by simp[l i j c]
 by_cases a:X (u,e)=0
 .by_cases b:X (u,f)=0
  .by_cases hg:X (u,g)=0
   .exfalso;apply n;ext ⟨i,j⟩;by_cases c:i=u
    .rcases m j with h | h | h | h<;>rw[c,h]
     .exact o a b hg
     .exact a
     .exact b
     .exact hg
    .exact l i j c
   .exact⟨(X (u,g))⁻¹•X,L.smul_mem _ d,k _,Or.inr (Or.inr ⟨by simp[a],by simp[b],by simp[hg]⟩)⟩
  .exact⟨(X (u,f))⁻¹•X,L.smul_mem _ d,k _,Or.inr (Or.inl ⟨by simp[a],by simp[b]⟩)⟩
 .exact⟨(X (u,e))⁻¹•X,L.smul_mem _ d,k _,Or.inl (by simp[a])⟩
def af3:W6:=by
 intro L hL X C U V W;obtain⟨f,G,R,u⟩:=U;obtain⟨g,H,S,v⟩:=V;obtain⟨h,J,T,e⟩:=W
 have w:f (1,0)=0->f (1,2)=0->f (1,3)=0->f (1,1)=0:=by
  intro d e2 k;have l:=hL f G;simp +decide only[p4,Bm,A1,A9,A8,u 0,u 2,u 3,
   d,e2,k,B8]at l
  grind
 have x:g (2,0)=0->g (2,1)=0->g (2,3)=0->g (2,2)=0:=by
  intro d i k;have l:=hL g H;simp +decide only[p4,Bm,A1,A9,A8,v 0,v 1,v 3,
   d,i,k,B8]at l
  grind
 have y:h (3,0)=0->h (3,1)=0->h (3,2)=0->h (3,3)=0:=by
  intro d i e2;have l:=hL h J;simp +decide only[p4,Bm,A1,A9,A8,e 0,e 1,e 2,
   d,i,e2,B8]at l
  grind
 obtain⟨a,D,n,O⟩:=VU L 1 0 2 3 f G R u (by decide) w
 obtain⟨b,E,o,P⟩:=VU L 2 0 1 3 g H S v (by decide) x
 obtain⟨c,F,p,Q⟩:=VU L 3 0 1 2 h J T e (by decide) y
 have K:a∈Ar L 0:=(ei L 0 a).2 ⟨D,λj=> n 0 j (by decide)⟩
 have M:b∈Ar L 0:=(ei L 0 b).2 ⟨E,λj=> o 0 j (by decide)⟩
 have N:c∈Ar L 0:=(ei L 0 c).2 ⟨F,λj=> p 0 j (by decide)⟩
 have q:=ans L hL (C 0) a b c D E F n o p;obtain⟨r,s,t,B,z,A,m⟩:=Vc _ _ _ (Rh L hL (C 0) a b c K M N);have d:=m 0;have i:=m 1;have e2:=m 2;have k:=m 3;clear m;simp +decide only[p4,m3,PV,Bm,A1,Fin.isValue,Fin.reduceAdd,A9,
  A8,n 0,n 2,n 3,o 0,o 1,o 3,p 0,p 1,p 2,C0,B8]at r s t B z A d i e2 k
 exact aek (a (1,0)) (a (1,1)) (a (1,2)) (a (1,3)) (b (2,0)) (b (2,1)) (b (2,2)) (b (2,3))
  (c (3,0)) (c (3,1)) (c (3,2)) (c (3,3))
  (by linear_combination r) (by linear_combination s) (by linear_combination t)
  (by linear_combination B- r- s) (by linear_combination z- r- t) (by linear_combination A- s- t)
  (by linear_combination d) (by linear_combination i) (by linear_combination e2) (by linear_combination k)
  (q 0 1 (by decide)) (q 0 2 (by decide)) (q 0 3 (by decide)) (q 1 2 (by decide)) (q 1 3 (by decide))
  (q 2 3 (by decide)) O P Q
def T4F (c:Fq) (Z X:Mt) (a b:ℂ): Prop :=
 MU 1 c+ a*MU 3 c=0/\MU 1 c+ b*MU 2 c=0/\p4 (Bm+ X)=65/\
 p4 (Bm+ M4 1 3 c a+ X)=65/\p4 (Bm+ M4 1 2 c b+ X)=65/\
 (∀ s:ℂ,p4 (Bm+ s•Z)=65)/\(∀ s:ℂ,p4 (Bm+ s•Z+ M4 1 3 c a)=65)/\
 (∀ s:ℂ,p4 (Bm+ s•Z+ M4 1 2 c b)=65)/\(∀ s:ℂ,p4 (Bm+ s•Z+ X)=65)
set_option maxHeartbeats 0 in
def WQ:(∀ (Z X:Mt) (b c:ℂ) (e:∀ i,Z (i,0)=0) (f:∀ i,Z (i,1)=0) (hp:Z (0,2)=1\/Z (1,2)=1\/Z (2,2)=1\/Z (3,2)=1\/Z (0,3)=1\/Z (1,3)=1\/Z (2,3)=1\/Z (3,3)=1) (d:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (H:T4F 0 Z X b c),False)/\(∀ (Z X:Mt) (b c:ℂ) (e:∀ i,Z (i,1)=0) (f:∀ i,Z (i,2)=0) (hp:Z (0,0)=1\/Z (1,0)=1\/Z (2,0)=1\/Z (3,0)=1\/Z (0,3)=1\/Z (1,3)=1\/Z (2,3)=1\/Z (3,3)=1) (d:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (H:T4F 1 Z X b c),False)/\(∀ (Z X:Mt) (b c:ℂ) (e:∀ i,Z (i,2)=0) (f:∀ i,Z (i,3)=0) (hp:Z (0,0)=1\/Z (1,0)=1\/Z (2,0)=1\/Z (3,0)=1\/Z (0,1)=1\/Z (1,1)=1\/Z (2,1)=1\/Z (3,1)=1) (d:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (H:T4F 2 Z X b c),False)/\(∀ (Z X:Mt) (b c:ℂ) (e:∀ i,Z (i,3)=0) (f:∀ i,Z (i,0)=0) (hp:Z (0,1)=1\/Z (1,1)=1\/Z (2,1)=1\/Z (3,1)=1\/Z (0,2)=1\/Z (1,2)=1\/Z (2,2)=1\/Z (3,2)=1) (d:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (H:T4F 3 Z X b c),False):=by
 refine⟨?_,?_,?_,?_⟩<;>intro Z X b c e f hp d a H;all_goals
  obtain⟨p,o,n,m,l,g,h,h3,k⟩:=H
  have z:=g 1;have A:=g 2;have B:=g 3;have C:=g 4
  have q:=h 1;have r:=h 2;have s:=h 3
  have t:=h3 1;have u:=h3 2;have v:=h3 3
  have w:=k 1;have x:=k 2;have y:=k 3
  clear g h h3 k
  simp +decide only[MU,p4,M4,E,Bm,A1,A4,A5,A9,A8,d 1,d 2,d 3,e,f,C0,B8,C3]at p o n m l z A B C q r s t u v w x y
  rcases a with a | ⟨a,m⟩ | ⟨a,m,l⟩<;>rcases hp with hp | hp | hp | hp | hp | hp | hp | hp<;>grind
def TY:(∀ (q:ℂ) (X:Mt) (l:q≠0) (h:q*MU 3 1- MU 3 0≠0) (n3:q*MU 2 1- MU 2 0≠0) (g:MU 1 0+ q*MU 1 1≠0) (b:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (f:p4 (Bm+ X)=65) (k:p4 (Bm+ aq 1 3 0 1 q+ aq 1 2 0 1 q)=65) (d:p4 (Bm+ aq 1 3 0 1 q+ X)=65) (e:p4 (Bm+ aq 1 2 0 1 q+ X)=65) (c:p4 (Bm+ aq 1 3 0 1 q+ aq 1 2 0 1 q+ X)=65),False)/\(∀ (q:ℂ) (X:Mt) (l:q≠0) (h:q*MU 3 2- MU 3 0≠0) (n3:q*MU 2 2- MU 2 0≠0) (g:MU 1 0+ q*MU 1 2≠0) (b:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (f:p4 (Bm+ X)=65) (k:p4 (Bm+ aq 1 3 0 2 q+ aq 1 2 0 2 q)=65) (d:p4 (Bm+ aq 1 3 0 2 q+ X)=65) (e:p4 (Bm+ aq 1 2 0 2 q+ X)=65) (c:p4 (Bm+ aq 1 3 0 2 q+ aq 1 2 0 2 q+ X)=65),False)/\(∀ (q:ℂ) (X:Mt) (l:q≠0) (h:q*MU 3 3- MU 3 0≠0) (n3:q*MU 2 3- MU 2 0≠0) (g:MU 1 0+ q*MU 1 3≠0) (b:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (f:p4 (Bm+ X)=65) (k:p4 (Bm+ aq 1 3 0 3 q+ aq 1 2 0 3 q)=65) (d:p4 (Bm+ aq 1 3 0 3 q+ X)=65) (e:p4 (Bm+ aq 1 2 0 3 q+ X)=65) (c:p4 (Bm+ aq 1 3 0 3 q+ aq 1 2 0 3 q+ X)=65),False)/\(∀ (q:ℂ) (X:Mt) (l:q≠0) (h:q*MU 3 2- MU 3 1≠0) (n3:q*MU 2 2- MU 2 1≠0) (g:MU 1 1+ q*MU 1 2≠0) (b:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (f:p4 (Bm+ X)=65) (k:p4 (Bm+ aq 1 3 1 2 q+ aq 1 2 1 2 q)=65) (d:p4 (Bm+ aq 1 3 1 2 q+ X)=65) (e:p4 (Bm+ aq 1 2 1 2 q+ X)=65) (c:p4 (Bm+ aq 1 3 1 2 q+ aq 1 2 1 2 q+ X)=65),False)/\(∀ (q:ℂ) (X:Mt) (l:q≠0) (h:q*MU 3 3- MU 3 1≠0) (n3:q*MU 2 3- MU 2 1≠0) (g:MU 1 1+ q*MU 1 3≠0) (b:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1) (f:p4 (Bm+ X)=65) (k:p4 (Bm+ aq 1 3 1 3 q+ aq 1 2 1 3 q)=65) (d:p4 (Bm+ aq 1 3 1 3 q+ X)=65) (e:p4 (Bm+ aq 1 2 1 3 q+ X)=65) (c:p4 (Bm+ aq 1 3 1 3 q+ aq 1 2 1 3 q+ X)=65),False):=by
 refine⟨?_,?_,?_,?_,?_⟩<;>intro q X l h n3 g b a f k d e c;all_goals
  simp +decide only[MU,p4,aq,E,Bm,A1,A4,A5,A9,A8,b 1,b 2,b 3,D7,C0,B8,C3]at h n3 g f k d e c
  rcases a with a | ⟨a,m⟩ | ⟨a,m,n⟩<;>grind
def akh (q:ℂ) (X:Mt) (m:q≠0) (n2:q*MU 3 3- MU 3 2≠0) (n3:q*MU 2 3- MU 2 2≠0)
  (h:MU 1 2+ q*MU 1 3≠0) (b:∀ i j,i≠0->X (i,j)=0) (a:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1)
  (g:p4 (Bm+ X)=65) (k:p4 (Bm+ aq 1 3 2 3 q+ aq 1 2 2 3 q)=65) (e:p4 (Bm+ aq 1 3 2 3 q+ X)=65)
  (f:p4 (Bm+ aq 1 2 2 3 q+ X)=65) (c:p4 (Bm+ aq 1 3 2 3 q+ aq 1 2 2 3 q+ X)=65):False:=by
 simp +decide only[MU,p4,aq,E,Bm,A1,A4,A5,A9,A8,b 1,b 2,b 3,D7,C0,B8,C3]at n2 n3 h g k e f c;rcases a with a | ⟨a,d⟩ | ⟨a,d,l⟩<;>grind
def NY (c d:Fq) (a b e:Nat):List P3:=
  [PS (Qi 2 3 c d (Vq a)) (Qi 1 3 c d (Vq b)),PS (Qi 2 3 c d (Vq a)) (Qi 1 2 c d (Vq e)),
   PS (Qi 1 3 c d (Vq b)) (Qi 1 2 c d (Vq e))]
def alC (c d t u:Fq) (s1 b s3 f a p:Nat) (Q:P1):Bool:=
 XE (R2 ((NY c d s1 b s3).getD f [])) ((NY c d s1 b s3).getD f []) &&
 XE (R2 ((NY c d s1 b s3).getD a [])) ((NY c d s1 b s3).getD a []) &&
 XE (R2 ((NY c d s1 b s3).getD p [])) ((NY c d s1 b s3).getD p []) &&
 UD (R2 ((NY c d s1 b s3).getD f [])) (R2 ((NY c d s1 b s3).getD a [])) (R2 ((NY c d s1 b s3).getD f []))
  (R2 ((NY c d s1 b s3).getD p [])) [] [] (oz (Nq (oz (oz [0,1] [-o5 u c,o5 u d]) [o5 t c,o5 t d]) 4) (oz Q Q)) 3
def vS (s:Nat) (X Y Z:ℂ):ℂ:=if s=0 then X else if s=1 then Y else Z
lemma aj9 (X Y Z:ℂ) (s:Nat):ew X Y Z (Vq s)=vS s X Y Z:=by
 unfold Vq vS;split_ifs<;>simp[ew,ly,gn,ld]
def VM (c d:Fq) (m n o:Nat) (X Y Z b e f:ℂ) (j:vS m X Y Z=b) (k:vS n X Y Z=e)
  (l:vS o X Y Z=f) (q:p4 (Bm+ aq 2 3 c d b+ aq 1 3 c d e)=65)
  (p:p4 (Bm+ aq 2 3 c d b+ aq 1 2 c d f)=65) (r:p4 (Bm+ aq 1 3 c d e+ aq 1 2 c d f)=65):
  ∀ i,ew X Y Z ((NY c d m n o).getD i [])=0:=by
 have a:∀ g h:Fq,∀ s:Nat,Ev X Y Z (Qi g h c d (Vq s))=aq g h c d (vS s X Y Z):=by
  intro g h s;funext t;simp only[Ev,abS,aj9]
 intro i;rcases i with _ | _ | _ | i
 .simp only[NY,L7];rw[RW,a,a,j,k,q,G4]
 .simp only[NY,P8,L7];rw[RW,a,a,j,l,p,G4]
 .simp only[NY,P8,L7];rw[RW,a,a,k,l,r,G4]
 .simp[NY,ZX]
def VN (c d t u:Fq) (h i j f a p:Nat) (Q:P1) (m:alC c d t u h i j f a p Q=true)
  (X Y Z b e g:ℂ) (w:vS h X Y Z=b) (x:vS i X Y Z=e) (y:vS j X Y Z=g)
  (v:p4 (Bm+ aq 2 3 c d b+ aq 1 3 c d e)=65) (s:p4 (Bm+ aq 2 3 c d b+ aq 1 2 c d g)=65)
  (C:p4 (Bm+ aq 1 3 c d e+ aq 1 2 c d g)=65)
  (z:X≠0) (A:X*MU u d- MU u c≠0) (B:MU t c+ X*MU t d≠0):gn X Q=0:=by
 by_contra l;have hL:=VM c d h i j X Y Z b e g w x y v s C;simp only[alC,D8]at m;obtain⟨⟨⟨r,D⟩,E⟩,k⟩:=m
 refine XJ _ _ _ _ [] [] _ 3 k X Y Z ?_ ?_ ?_ ?_ (by simp[M6,ew,ly,gn,ld])
  (by simp[M6,ew,ly,gn,ld]) ?_
 .rw[LD _ _ r];exact hL f
 .rw[LD _ _ D];exact hL a
 .rw[LD _ _ r];exact hL f
 .rw[LD _ _ E];exact hL p
 .have n:gn X [0,1]=X:=by simp[gn,ld]
  have o:gn X [-o5 u c,o5 u d]=X*MU u d- MU u c:=by simp[gn,ld,Va]<;>ring
  have q:gn X [o5 t c,o5 t d]=MU t c+ X*MU t d:=by simp[gn,ld,Va]<;>ring
  have :ew X Y Z (lx (oz (Nq (oz (oz [0,1] [-o5 u c,o5 u d]) [o5 t c,o5 t d]) 4) (oz Q Q)))=
    (gn X [0,1]*gn X [-o5 u c,o5 u d]*gn X [o5 t c,o5 t d])^4*(gn X Q*gn X Q):=by
   simp only[lx,ew,ly,ld,Rz,Lj,C3,B8]
  rw[this,n,o,q];exact mul_ne_zero (N4 4 (mul_ne_zero (mul_ne_zero z A) B)) (mul_ne_zero l l)
def ahz (F B:P3) (Q:P1) (r:P3× P3× P2) (s:P1× P1× P1):Bool:=
 aaX [(r.1,F),(r.2.1,B),(Mb,Kz r.2.2)] && decide (r.2.2.length≤1) &&
 aaX [(lx s.1,lx (r.2.2.getD 0 [])),(lx s.2.1,lx Q),(Mb,lx s.2.2)] &&
 decide (s.2.2.length=1) && s.2.2.headD 0 !=0
def ahy (F B:P3) (Q:P1):Bool:=ahz F B Q (ZW F B) (YE ((ZW F B).2.2.getD 0 []) Q)
def Vi (F B:P3) (Q:P1) (h:ahy F B Q=true) (x y z:ℂ) (hF:ew x y z F=0)
  (f:ew x y z B=0) (i:gn x Q=0):False:=by
 unfold ahy at h;generalize YE ((ZW F B).2.2.getD 0 []) Q=s at h;generalize ZW F B=r at h;obtain⟨u,w,R⟩:=r;obtain⟨S,T,G⟩:=s;simp only[ahz,D8,N5,L4,D7]at h;obtain⟨⟨⟨⟨l,k⟩,m⟩,d⟩,e⟩:=h;have b:=rz _ l x y z;have a:=rz _ m x y z;simp only[L1,List.map_nil,N3,List.sum_nil,B8,Yz,hF,f,C3,
  C0]at b a
 have j:ew x y z (lx (R.getD 0 []))=0:=by
  rcases R with _ | ⟨V,_ | ⟨_,_⟩⟩
  .simp[lx,ew,ly,gn,ld]
  .simp only[lx,Kz,L7]at b ⊢;grind
  .simp at k
 have c:ew x y z (lx Q)=0:=by simp only[lx,ew,ly,ld,C3,B8];exact i
 rw[j,c]at a;rcases G with _ | ⟨g,_ | ⟨_,_⟩⟩<;>simp at d
 exact e (by simpa[lx,ew,ly,gn,ld] using a)
def akb (a b c:ℂ) (h:a≠0) (f:a*11-11≠0) (g:11+ a*11≠0) (n:b≠0) (m:b*11-11≠0) (j:11+ b*16≠0) (o:c≠0) (k:c*11-11≠0) (l:11+ c*16≠0)
  (e:p4 (Bm+(aq 2 3 0 1 a)+(aq 1 3 0 1 b))=65) (d:p4 (Bm+(aq 2 3 0 1 a)+(aq 1 2 0 1 c))=65) (i:p4 (Bm+(aq 1 3 0 1 b)+(aq 1 2 0 1 c))=65):False:=
 by simpa[gn,ld] using VN 0 1 2 3 0 1 2 2 1 0 [1] (by decide +kernel) a b c a b c rfl rfl rfl e d i h f g
def akc (a b c:ℂ) (o:a≠0) (j:a*11-11≠0) (l:11+ a*16≠0) (h:b≠0) (g:b*11-11≠0) (d:11+ b*11≠0) (n:c≠0) (k:c*16-11≠0) (m:11+ c*11≠0)
  (f:p4 (Bm+(aq 2 3 0 2 a)+(aq 1 3 0 2 b))=65) (e:p4 (Bm+(aq 2 3 0 2 a)+(aq 1 2 0 2 c))=65) (i:p4 (Bm+(aq 1 3 0 2 b)+(aq 1 2 0 2 c))=65):False:=
 by simpa[gn,ld] using VN 0 2 1 3 2 0 1 1 0 2 [1] (by decide +kernel) b c a a b c rfl rfl rfl f e i h g d
def akd (a b c:ℂ) (o:a≠0) (k:a*16-11≠0) (l:11+ a*11≠0) (n:b≠0) (m:b*16-11≠0) (j:11+ b*11≠0) (h:c≠0) (f:c*11-11≠0) (g:11+ c*11≠0)
  (e:p4 (Bm+(aq 2 3 0 3 a)+(aq 1 3 0 3 b))=65) (d:p4 (Bm+(aq 2 3 0 3 a)+(aq 1 2 0 3 c))=65) (i:p4 (Bm+(aq 1 3 0 3 b)+(aq 1 2 0 3 c))=65):False:=
 by simpa[gn,ld] using VN 0 3 1 2 1 2 0 0 2 1 [1] (by decide +kernel) c a b a b c rfl rfl rfl e d i h f g
def ake (a b c:ℂ) (l:a≠0) (g:a*11-11≠0) (i:11+ a*16≠0) (o:b≠0) (n:b*11-11≠0) (m:16+ b*11≠0) (k:c≠0) (h:c*16-11≠0) (j:16+ c*11≠0)
  (e:p4 (Bm+(aq 2 3 1 2 a)+(aq 1 3 1 2 b))=65) (d:p4 (Bm+(aq 2 3 1 2 a)+(aq 1 2 1 2 c))=65) (f:p4 (Bm+(aq 1 3 1 2 b)+(aq 1 2 1 2 c))=65):False:=
 Vi [[[-5]],[[-54]],[[5]]] ((NY 1 2 0 1 2).getD 1 []) [352,-2616,77] (by decide +kernel) a b c
  (by simpa[ew,ly,gn,ld] using VN 1 2 1 2 1 2 0 0 2 1 [-5,-54,5] (by decide +kernel) c a b a b c rfl rfl rfl e d f k h j)
  (VM 1 2 0 1 2 a b c a b c rfl rfl rfl e d f 1)
  (VN 1 2 2 3 0 1 2 2 1 0 [352,-2616,77] (by decide +kernel) a b c a b c rfl rfl rfl e d f l g i)
def akf (a b c:ℂ) (l:a≠0) (g:a*16-11≠0) (i:11+ a*11≠0) (o:b≠0) (n:b*16-11≠0) (m:16+ b*11≠0) (k:c≠0) (h:c*11-11≠0) (j:16+ c*11≠0)
  (e:p4 (Bm+(aq 2 3 1 3 a)+(aq 1 3 1 3 b))=65) (d:p4 (Bm+(aq 2 3 1 3 a)+(aq 1 2 1 3 c))=65) (f:p4 (Bm+(aq 1 3 1 3 b)+(aq 1 2 1 3 c))=65):False:=
 Vi [[[77]],[[-2616]],[[352]]] ((NY 1 3 0 1 2).getD 1 []) [352,2616,77] (by decide +kernel) a b c
  (by simpa[ew,ly,gn,ld] using VN 1 3 1 2 1 2 0 0 2 1 [77,-2616,352] (by decide +kernel) c a b a b c rfl rfl rfl e d f k h j)
  (VM 1 3 0 1 2 a b c a b c rfl rfl rfl e d f 1)
  (VN 1 3 2 3 0 1 2 2 1 0 [352,2616,77] (by decide +kernel) a b c a b c rfl rfl rfl e d f l g i)
def akg (a b c:ℂ) (l:a≠0) (g:a*16-11≠0) (i:16+ a*11≠0) (o:b≠0) (n:b*16-11≠0) (m:11+ b*11≠0) (k:c≠0) (h:c*11-16≠0) (j:11+ c*11≠0)
  (e:p4 (Bm+(aq 2 3 2 3 a)+(aq 1 3 2 3 b))=65) (d:p4 (Bm+(aq 2 3 2 3 a)+(aq 1 2 2 3 c))=65) (f:p4 (Bm+(aq 1 3 2 3 b)+(aq 1 2 2 3 c))=65):False:=
 Vi [[[77]],[[2616]],[[352]]] ((NY 2 3 0 1 2).getD 1 []) [-5,-54,5] (by decide +kernel) a b c
  (by simpa[ew,ly,gn,ld] using VN 2 3 1 2 1 2 0 0 2 1 [77,2616,352] (by decide +kernel) c a b a b c rfl rfl rfl e d f k h j)
  (VM 2 3 0 1 2 a b c a b c rfl rfl rfl e d f 1)
  (VN 2 3 2 3 0 1 2 2 1 0 [-5,-54,5] (by decide +kernel) a b c a b c rfl rfl rfl e d f l g i)
def adv (L:Sq) (p:∀ t∈L,p4 (Bm+ t)=65) (c d:Fq) (u:c< d)
  (r s g3:Mt) (x:r∈L) (y:s∈L) (m3:g3∈L)
  (B1:Ke 2 3 c d r) (B2:Ke 1 3 c d s) (B3:Ke 1 2 c d g3):False:=by
 have q:c≠d:=D5 u
 obtain⟨F,m,A,l,na1,i,C,a⟩:=ME L p 2 3 c d (by decide) q r x B1
 obtain⟨G,n,z,j,e,h,D,b⟩:=ME L p 1 3 c d (by decide) q s y B2
 obtain⟨H,o,B,k,f,g,E,o7⟩:=ME L p 1 2 c d (by decide) q g3 m3 B3
 have P:∀ X Y:Mt,X∈L->Y∈L->p4 (Bm+ X+ Y)=65:=
  λX Y v w=> by rw[D1];exact p _ (L.add_mem v w)
 fin_cases c<;>fin_cases d<;>(try exact absurd u (by decide))
 .exact akb m n o l na1 i j e h k f g (P _ _ a b) (P _ _ a o7) (P _ _ b o7)
 .exact akc m n o l na1 i j e h k f g (P _ _ a b) (P _ _ a o7) (P _ _ b o7)
 .exact akd m n o l na1 i j e h k f g (P _ _ a b) (P _ _ a o7) (P _ _ b o7)
 .exact ake m n o l na1 i j e h k f g (P _ _ a b) (P _ _ a o7) (P _ _ b o7)
 .exact akf m n o l na1 i j e h k f g (P _ _ a b) (P _ _ a o7) (P _ _ b o7)
 .exact akg m n o l na1 i j e h k f g (P _ _ a b) (P _ _ a o7) (P _ _ b o7)
def aaJ (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65) (l:finrank ℂ L=6) (c:Fq)
  (p q X:Mt) (y:p∈L) (m3:q∈L) (S2:Mc 1 3 c p) (S3:Mc 1 2 c q)
  (o:X∈L) (m:∀ i j,i≠0->X (i,j)=0)
  (n:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1):False:=by
 obtain⟨y2,v,n2⟩:=WM L b 1 3 c (by decide) p y S2
 obtain⟨k,r,u⟩:=WM L b 1 2 c (by decide) q m3 S3
 have P:∀ A B:Mt,A∈L->B∈L->p4 (Bm+ A+ B)=65:=
  λA B w x=> by rw[D1];exact b _ (L.add_mem w x)
 have F:∀ Z∈L,T4F c Z X y2 k:=λZ a=>
  ⟨v,r,b X o,P _ _ n2 o,P _ _ u o,λs=> b _ (L.smul_mem s a),
   λs=> P _ _ (L.smul_mem s a) n2,λs=> P _ _ (L.smul_mem s a) u,
   λs=> P _ _ (L.smul_mem s a) o⟩
 fin_cases c
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b l 0 1 (by decide)
  obtain⟨Z,a,g,h,zp⟩:=Pn L 0 1 2 3 (by decide) Y d h0 e f
  exact WQ.1 Z X y2 k g h zp m n (F Z a)
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b l 1 2 (by decide)
  obtain⟨Z,a,g,h,zp⟩:=Pn L 1 2 0 3 (by decide) Y d h0 e f
  exact WQ.2.1 Z X y2 k g h zp m n (F Z a)
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b l 2 3 (by decide)
  obtain⟨Z,a,g,h,zp⟩:=Pn L 2 3 0 1 (by decide) Y d h0 e f
  exact WQ.2.2.1 Z X y2 k g h zp m n (F Z a)
 .obtain⟨Y,d,h0,e,f⟩:=Uc L b l 3 0 (by decide)
  obtain⟨Z,a,g,h,zp⟩:=Pn L 3 0 1 2 (by decide) Y d h0 e f
  exact WQ.2.2.2 Z X y2 k g h zp m n (F Z a)
lemma ach (t u c d:Fq) (q:ℂ) (b:t≠u) (a:c≠d):
  aq t u c d q (t,c)=q*MU u d- MU u c:=by
 simp[aq,E,b,a]
lemma aci (t u c d:Fq) (q:ℂ) (b:t≠u) (a:c≠d):
  aq t u c d q (t,d)=q*(q*MU u d- MU u c):=by
 simp[aq,E,b,a.symm]
def adw (L:Sq) (hL:∀ t∈L,p4 (Bm+ t)=65) (c d:Fq) (s:c< d)
  (n o X:Mt) (G:n∈L) (m3:o∈L) (B2:Ke 1 3 c d n) (B3:Ke 1 2 c d o)
  (par:∀ a b,n (1,a)*o (1,b)=n (1,b)*o (1,a))
  (mX:X∈L) (l:∀ i j,i≠0->X (i,j)=0)
  (m:X (0,1)=1\/X (0,1)=0/\X (0,2)=1\/X (0,1)=0/\X (0,2)=0/\X (0,3)=1):False:=by
 have Nd:c≠d:=D5 s
 obtain⟨E,g,u,k,f,Ij,w,n2⟩:=ME L hL 1 3 c d (by decide) Nd n G B2
 obtain⟨F,p,v,J,e,H,x,n3⟩:=ME L hL 1 2 c d (by decide) Nd o m3 B3
 have D:p=g:=by
  have h:=par c d;rw[w,x]at h;simp only[A4,A5]at h
  rw[ach 1 3 c d g (by decide) Nd,aci 1 3 c d g (by decide) Nd,ach 1 2 c d p (by decide) Nd,
   aci 1 2 c d p (by decide) Nd]at h
  have y:(E*F*(g*MU 3 d- MU 3 c)*(p*MU 2 d- MU 2 c))*(p- g)=0:=by
   grind
  have K:=(A0.1 y).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero u v) f) e);grind
 rw[D]at n3 e;have P:∀ A B:Mt,A∈L->B∈L->p4 (Bm+ A+ B)=65:=
  λA B q r=> by rw[D1];exact hL _ (L.add_mem q r)
 have P3:∀ A B C:Mt,A∈L->B∈L->C∈L->p4 (Bm+ A+ B+ C)=65:=
  λA B C q r z=> by rw[D1,D1];exact hL _ (L.add_mem q (L.add_mem r z))
 fin_cases c<;>fin_cases d<;>(try exact absurd s (by decide))
 .exact TY.1 g X k f e Ij l m (hL X mX) (P _ _ n2 n3) (P _ _ n2 mX) (P _ _ n3 mX) (P3 _ _ _ n2 n3 mX)
 .exact TY.2.1 g X k f e Ij l m (hL X mX) (P _ _ n2 n3) (P _ _ n2 mX) (P _ _ n3 mX) (P3 _ _ _ n2 n3 mX)
 .exact TY.2.2.1 g X k f e Ij l m (hL X mX) (P _ _ n2 n3) (P _ _ n2 mX) (P _ _ n3 mX) (P3 _ _ _ n2 n3 mX)
 .exact TY.2.2.2.1 g X k f e Ij l m (hL X mX) (P _ _ n2 n3) (P _ _ n2 mX) (P _ _ n3 mX) (P3 _ _ _ n2 n3 mX)
 .exact TY.2.2.2.2 g X k f e Ij l m (hL X mX) (P _ _ n2 n3) (P _ _ n2 mX) (P _ _ n3 mX) (P3 _ _ _ n2 n3 mX)
 .exact akh g X k f e Ij l m (hL X mX) (P _ _ n2 n3) (P _ _ n2 mX) (P _ _ n3 mX) (P3 _ _ _ n2 n3 mX)
def nS (L:Sq) (u:Fq) (h:¬ Kq L u):
  ∀ X∈L,(∀ i j,i≠u->X (i,j)=0)->X=0:=
 λX b c=> by by_contra a;exact h ⟨X,b,a,c⟩
def Ua (L:Sq) (E:∀ t∈L,p4 (Bm+ t)=65) (D:finrank ℂ L=6)
  (x:∀ r,finrank ℂ (L.map (af r))=3)
  (r s t u:Fq) (p:r< s) (l:t< u) (q:r≠t) (v:r≠u) (w:s≠t) (n:s≠u)
  (y:∀ X∈L,(∀ i j,i≠t->X (i,j)=0)->X=0) (z:∀ X∈L,(∀ i j,i≠u->X (i,j)=0)->X=0)
  (H:finrank ℂ (Kp L r s)=1) (g:Mt) (A:g∈Kp L r s) (c:g≠0):
  ∃ J,ot t u J g:=by
 obtain⟨k,d,e⟩:=(Kd L r s g).1 A;have o:=OZ _ H g A c;have F:=N1 L E D r s t u p l q v w n (x r) (x s) g k d e c
  (λY G B C=> o Y ((Kd L r s Y).2 ⟨G,B,C⟩))
 have f:=aco r s t u (D5 p) q v w n (D5 l);apply SR;apply XH t u (D5 l) g
 .intro i j b h;rcases f i with rfl | rfl | rfl | rfl
  .exact d j
  .exact e j
  .exact absurd rfl b
  .exact absurd rfl h
 .exact Z8 t u g F
 .by_contra a;apply c;apply z g k;intro i j h;rcases f i with rfl | rfl | rfl | rfl
  .exact d j
  .exact e j
  .by_contra m;exact a ⟨j,m⟩
  .exact absurd rfl h
 .by_contra a;apply c;apply y g k;intro i j b;rcases f i with rfl | rfl | rfl | rfl
  .exact d j
  .exact e j
  .exact absurd rfl b
  .by_contra m;exact a ⟨j,m⟩
def apr (L:Sq) (l:finrank ℂ L=6) (m:∀ r,finrank ℂ (L.map (af r))=3)
  (s t u:Fq) (d:∀ i:Fq,i=0\/i=s\/i=t\/i=u)
  (a:∀ X∈L,(∀ i j,i≠u->X (i,j)=0)->X=0)
  (h:2≤ finrank ℂ (Kp L 0 s)) (k:2≤ finrank ℂ (Kp L 0 t)):False:=by
 obtain⟨X,n,e⟩:=Uy (Ar L 0) (Kp L 0 s) (Kp L 0 t) (MF L l 0 (m 0))
  inf_le_left inf_le_left h k
 obtain⟨p,q⟩:=A6.1 n;obtain⟨f,o,b⟩:=(Kd L 0 s X).1 p;obtain⟨-,-,c⟩:=(Kd L 0 t X).1 q;apply e;apply a X f;intro i j g;rcases d i with rfl | rfl | rfl | rfl
 .exact o j
 .exact b j
 .exact c j
 .exact absurd rfl g
def Vb (F:∀ i:Fin 186,ak (rA i) (rB i) (rC i))
  (L:Sq) (f:∀ t∈L,p4 (Bm+ t)=65) (g:finrank ℂ L=6)
  (m:∀ r,finrank ℂ (L.map (af r))=3) (T:Kq L 0) (Q:¬ Kq L 1) (R:¬ Kq L 2)
  (S:¬ Kq L 3) (M:finrank ℂ (Kp L 0 2)=1) (N:finrank ℂ (Kp L 0 3)=1):False:=by
 obtain⟨k,s,C,zX1⟩:=T
 have E:k (0,1)=0->k (0,2)=0->k (0,3)=0->k (0,0)=0:=by
  intro u v O;have l:=f k s;simp +decide only[p4,Bm,A1,A9,A8,zX1 1,zX1 2,zX1 3,
   u,v,O,B8]at l
  grind
 obtain⟨X,z,w,x⟩:=VU L 0 1 2 3 k s C zX1 (by decide) E
 have S1:=nS L 1 Q;have S2:=nS L 2 R;have S3:=nS L 3 S
 obtain⟨b,o,D⟩:=dk (K:=Kp L 0 2) (by omega)
 obtain⟨c,p,z3⟩:=dk (K:=Kp L 0 3) (by omega)
 obtain⟨QX,d⟩:=Ua L f g m 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) S1 S3 M b o D
 obtain⟨n,a⟩:=Ua L f g m 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) S1 S2 N c p z3
 have q:=((Kd L 0 2 b).1 o).1;have L3:=((Kd L 0 3 c).1 p).1;by_cases A:2≤ finrank ℂ (Kp L 0 1)
 .have e:QX=n:=Qz 1 3 1 2 QX n b c d a
   (Yo L g m 0 1 2 3 A b c o p D z3 (λj=>(Mi 1 3 QX b d j).1)
    (λj=>(Mi 1 2 n c a j).1))
  rw[<- e]at a;by_cases h:QX.val<4
  .simp only[ot,h,A9]at d a;exact aaJ L f g (iz QX) b c X q L3 d a z w x
  .simp only[ot,h,A8]at d a;exact adw L f (iz QX) (mr QX) (Sy QX h) b c X q L3 d a
    (Rx L g m 0 1 2 3 A b c o p) z w x
 .have J:finrank ℂ (Kp L 0 1)=1:=by have :=TE L f g 0 1 (by decide);omega
  obtain⟨g1,y,U⟩:=dk (K:=Kp L 0 1) (by omega)
  obtain⟨U9,T1⟩:=Ua L f g m 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) S2 S3 J g1 y U
  have G:=((Kd L 0 1 g1).1 y).1;have P:Lq g1 b c:=Rh L f (m 0) g1 b c (A6.1 y).1
   (A6.1 o).1 (A6.1 p).1
  have H:U9=QX/\QX=n:=by
   by_contra B;exact UN F U9 QX n B g1 b c T1 d a P
  obtain⟨u,v⟩:=H;rw[<- v]at a;rw[<- u]at d a;by_cases h:U9.val<4
  .simp only[ot,h,A9]at d a;exact aaJ L f g (iz U9) b c X q L3 d a z w x
  .simp only[ot,h,A8]at T1 d a;exact adv L f (iz U9) (mr U9) (Sy U9 h) g1 b c G q L3 T1 d a
def af2 (j:∀ i:Fin 186,ak (rA i) (rB i) (rC i)):W5:=by
 intro L e b d l f g n3;have m:∀ s t u:Fq,(∀ i:Fq,i=0\/i=s\/i=t\/i=u)-> ¬ Kq L u->
   2≤ finrank ℂ (Kp L 0 s)->2≤ finrank ℂ (Kp L 0 t)->False:=
  λs t u v w q r=> apr L b d s t u v (nS L u w) q r
 have a:∀ s:Fq,s≠0-> ¬ 2≤ finrank ℂ (Kp L 0 s)->finrank ℂ (Kp L 0 s)=1:=
  λs h hn=> by have :=TE L e b 0 s (Ne.symm h);omega
 by_cases c:2≤ finrank ℂ (Kp L 0 2)
 .have k:finrank ℂ (Kp L 0 1)=1:=a 1 (by decide) (λh=> m 1 2 3 (by decide) n3 h c)
  have p:finrank ℂ (Kp L 0 3)=1:=a 3 (by decide) (λh=> m 2 3 1 (by decide) f c h)
  exact Vb j (L.map (gp (swap 1 2))) (LY L e _) (by rw[o6];exact b)
   (Pg L _ d) (ou L _ 0 0 (by decide) l) (mo L _ 2 1 (by decide) g)
   (mo L _ 1 2 (by decide) f) (mo L _ 3 3 (by decide) n3)
   (by rw[SO L _ 0 1 0 2 (by decide) (by decide)];exact k)
   (by rw[SO L _ 0 3 0 3 (by decide) (by decide)];exact p)
 .by_cases n:2≤ finrank ℂ (Kp L 0 3)
  .have k:finrank ℂ (Kp L 0 1)=1:=a 1 (by decide) (λh=> m 1 3 2 (by decide) g h n)
   have o:finrank ℂ (Kp L 0 2)=1:=a 2 (by decide) c
   exact Vb j (L.map (gp (swap 1 3))) (LY L e _) (by rw[o6];exact b)
    (Pg L _ d) (ou L _ 0 0 (by decide) l) (mo L _ 3 1 (by decide) n3)
    (mo L _ 2 2 (by decide) g) (mo L _ 1 3 (by decide) f)
    (by rw[SO L _ 0 2 0 2 (by decide) (by decide)];exact o)
    (by rw[SO L _ 0 1 0 3 (by decide) (by decide)];exact k)
  .exact Vb j L e b d l f g n3 (a 2 (by decide) c) (a 3 (by decide) n)
lemma ajD (a:RE) (b:Q7):
  ¬ (∃ L:Submodule ℂ (Fq× Fq->ℂ),finrank ℂ L=6/\ ∀ t∈L,
   permanent (Matrix.of λ(i j:Fq)=>(if i=j then (2:ℂ) else 1)+ t (i,j))=65):=
 Xo Ws (af2 Ws) a af3 b
def Sw {ι: Type} [Fintype ι] [DecidableEq ι] (A B:Submodule ℂ (ι->ℂ))
  (h:∀ a∈A,∀ b∈B,dotProduct a b=0):
  finrank ℂ A+ finrank ℂ B≤ Fintype.card ι:=by
 set W:Submodule ℂ (Module.Dual ℂ (ι->ℂ)):=A.map (dotProductEquiv ℂ ι).toLinearMap with i;have d:finrank ℂ W=finrank ℂ A:=L6 (dotProductEquiv ℂ ι) A;have c:=Subspace.finrank_add_finrank_dualCoannihilator_eq W;rw[d,Module.finrank_fintype_fun_eq_card]at c
 have e:B≤ W.dualCoannihilator:=by
  intro x hx;rw[Submodule.mem_dualCoannihilator];intro φ f;obtain⟨a,g,rfl⟩:=B6.1 f;simpa[dotProductEquiv] using h a g x hx
 have :=E7 e;omega
abbrev Ft:=Fin 3
def p3 (M:Ft× Ft->ℂ):ℂ:=
 M (0,0)*M (1,1)*M (2,2)+ M (0,0)*M (1,2)*M (2,1)+
 M (0,1)*M (1,0)*M (2,2)+ M (0,1)*M (1,2)*M (2,0)+
 M (0,2)*M (1,0)*M (2,1)+ M (0,2)*M (1,1)*M (2,0)
def bn (c:Fq):Equiv.Perm (Fq):=if c=0 then 1 else swap 0 1
abbrev B9:=Ft× Ft->ℂ
def j1 (z:Ft->ℂ):Ft->Ft->ℂ:= ![![0,z 2,z 1],![z 2,0,z 0],![z 1,z 0,0]]
def ah:Ft->Fin 2->Ft:= ![![1,2],![0,2],![0,1]]
def Qf (z w:Ft->ℂ) (M:B9):ℂ:=
 ∑ i:Ft,∑ j:Ft,z i*w j*
  (M (ah i 0,ah j 0)*M (ah i 1,ah j 1)+ M (ah i 0,ah j 1)*M (ah i 1,ah j 0))
def rR:Ft->Fq:= ![1,2,3]
def dq (c:Fq):Mt→ₗ[ℂ] B9 where
 toFun X q:=X (rR q.1,bn c (rR q.2))
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def I7 (c:Fq) (a:c.val<2):c=0\/c=1:=by fin_cases c<;>simp at a ⊢
structure V4 where
 x0:ℂ
 x1:ℂ
 x2:ℂ
 x3:ℂ
def B0:V4:=⟨2,1,1,1⟩
def B1:V4:=⟨1,2,1,1⟩
def B2:V4:=⟨1,1,2,1⟩
def B3:V4:=⟨1,1,1,2⟩
def zv (a b c:ℂ):V4:=⟨-11*(a+ b+ c),16*a,16*b,16*c⟩
def yv (a b c:ℂ):V4:=⟨-(16*a+11*b+11*c),11*a,11*b,11*c⟩
def mp (a b c d:V4):ℂ:=
 (a.x0*b.x1+ a.x1*b.x0)*(c.x2*d.x3+ c.x3*d.x2)+
 (a.x0*b.x2+ a.x2*b.x0)*(c.x1*d.x3+ c.x3*d.x1)+
 (a.x0*b.x3+ a.x3*b.x0)*(c.x1*d.x2+ c.x2*d.x1)+
 (a.x1*b.x2+ a.x2*b.x1)*(c.x0*d.x3+ c.x3*d.x0)+
 (a.x1*b.x3+ a.x3*b.x1)*(c.x0*d.x2+ c.x2*d.x0)+
 (a.x2*b.x3+ a.x3*b.x2)*(c.x0*d.x1+ c.x1*d.x0)
def me (a b c:V4):ℂ:=a.x1*b.x2*c.x3+ a.x1*b.x3*c.x2+ a.x2*b.x1*c.x3+ a.x2*b.x3*c.x1+ a.x3*b.x1*c.x2+ a.x3*b.x2*c.x1
def lu (a b c:V4):ℂ:=a.x0*b.x2*c.x3+ a.x0*b.x3*c.x2+ a.x2*b.x0*c.x3+ a.x2*b.x3*c.x0+ a.x3*b.x0*c.x2+ a.x3*b.x2*c.x0
def mh (a b c:V4):ℂ:=a.x0*b.x1*c.x3+ a.x0*b.x3*c.x1+ a.x1*b.x0*c.x3+ a.x1*b.x3*c.x0+ a.x3*b.x0*c.x1+ a.x3*b.x1*c.x0
def mj (a b c:V4):ℂ:=a.x0*b.x1*c.x2+ a.x0*b.x2*c.x1+ a.x1*b.x0*c.x2+ a.x1*b.x2*c.x0+ a.x2*b.x0*c.x1+ a.x2*b.x1*c.x0
def QF (z y d e b c t a:V4): Prop :=
 mp B0 B1 a B3+ mp B0 c B2 B3+ mp b B1 B2 B3=0/\
 mp B0 c a B3+ mp b B1 a B3+ mp b c B2 B3=0/\
 mp b c a B3=0/\
 mp B0 B1 B2 t+ mp B0 e B2 B3+ mp d B1 B2 B3=0/\
 mp B0 B1 a t+ mp B0 e a B3+ mp B0 c B2 t+ mp d B1 a B3+ mp d c B2 B3+ mp b B1 B2 t+ mp b e B2 B3=0/\
 mp B0 c a t+ mp d c a B3+ mp b B1 a t+ mp b e a B3+ mp b c B2 t=0/\
 mp b c a t=0/\
 mp B0 e B2 t+ mp d B1 B2 t+ mp d e B2 B3=0/\
 mp B0 e a t+ mp d B1 a t+ mp d e a B3+ mp d c B2 t+ mp b e B2 t=0/\
 mp d c a t+ mp b e a t=0/\
 mp d e B2 t=0/\
 mp d e a t=0/\
 mp B0 y B2 B3=0/\
 mp B0 y a B3+ mp b y B2 B3=0/\
 mp b y a B3=0/\
 mp B0 y B2 t+ mp d y B2 B3=0/\
 mp B0 y a t+ mp d y a B3+ mp b y B2 t=0/\
 mp b y a t=0/\
 mp d y B2 t=0/\
 mp d y a t=0/\
 mp z B1 B2 B3=0/\
 mp z B1 a B3+ mp z c B2 B3=0/\
 mp z c a B3=0/\
 mp z B1 B2 t+ mp z e B2 B3=0/\
 mp z B1 a t+ mp z e a B3+ mp z c B2 t=0/\
 mp z c a t=0/\
 mp z e B2 t=0/\
 mp z e a t=0/\
 mp z y B2 B3=0/\
 mp z y a B3=0/\
 mp z y B2 t=0/\
 mp z y a t=0
def O2 (z y d e b c t a:V4): Prop :=
 me z y t=0/\
 lu z y t=0/\
 mh z y t=0/\
 mj z y t=0/\
 me z e t=0/\
 lu z e t=0/\
 mh z e t=0/\
 mj z e t=0/\
 me d y t=0/\
 lu d y t=0/\
 mh d y t=0/\
 mj d y t=0/\
 me d e t=0/\
 lu d e t=0/\
 mh d e t=0/\
 mj d e t=0/\
 me z y a=0/\
 lu z y a=0/\
 mh z y a=0/\
 mj z y a=0/\
 me z c a=0/\
 lu z c a=0/\
 mh z c a=0/\
 mj z c a=0/\
 me b y a=0/\
 lu b y a=0/\
 mh b y a=0/\
 mj b y a=0/\
 me b c a=0/\
 lu b c a=0/\
 mh b c a=0/\
 mj b c a=0
def Rg (z y t a:V4): Prop :=
 z.x0*y.x0*t.x0*a.x0=0/\
 z.x1*y.x1*t.x1*a.x1=0/\
 z.x2*y.x2*t.x2*a.x2=0/\
 z.x3*y.x3*t.x3*a.x3=0
def Iw (z y d e b c t a:V4): Prop :=
 QF z y d e b c t a/\O2 z y d e b c t a/\Rg z y t a
def TH (z y x0 x1 a b:V4): Prop :=
 mp B0 B1 B2 b+ mp B0 B1 a B3=0/\
 mp B0 B1 a b=0/\
 mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0/\
 mp B0 x1 B2 b+ mp B0 x1 a B3+ mp x0 B1 B2 b+ mp x0 B1 a B3=0/\
 mp B0 x1 a b+ mp x0 B1 a b=0/\
 mp x0 x1 B2 B3=0/\
 mp x0 x1 B2 b+ mp x0 x1 a B3=0/\
 mp x0 x1 a b=0/\
 mp B0 y B2 B3=0/\
 mp B0 y B2 b+ mp B0 y a B3=0/\
 mp B0 y a b=0/\
 mp x0 y B2 B3=0/\
 mp x0 y B2 b+ mp x0 y a B3=0/\
 mp x0 y a b=0/\
 mp z B1 B2 B3=0/\
 mp z B1 B2 b+ mp z B1 a B3=0/\
 mp z B1 a b=0/\
 mp z x1 B2 B3=0/\
 mp z x1 B2 b+ mp z x1 a B3=0/\
 mp z x1 a b=0/\
 mp z y B2 B3=0/\
 mp z y B2 b+ mp z y a B3=0/\
 mp z y a b=0
def Ri (z y a b:V4): Prop :=
 me y a b=0/\
 lu y a b=0/\
 mh y a b=0/\
 mj y a b=0/\
 me z a b=0/\
 lu z a b=0/\
 mh z a b=0/\
 mj z a b=0
def Yy (z y x0 x1 a b:V4): Prop :=
 mp z y B2 B3=0/\
 mp z y a b=0/\
 mp z y B2 b+ mp z y a B3=0/\
 mp z x1 B2 B3=0/\
 mp z x1 a b=0/\
 mp z x1 B2 b+ mp z x1 a B3=0/\
 mp x0 y B2 B3=0/\
 mp x0 y a b=0/\
 mp x0 y B2 b+ mp x0 y a B3=0/\
 mp x0 x1 B2 B3=0/\
 mp x0 x1 a b=0/\
 mp x0 x1 B2 b+ mp x0 x1 a B3=0
def Mh (z y x0 x1 a b:V4): Prop :=
 TH z y x0 x1 a b/\Ri z y a b/\Yy z y x0 x1 a b
def va (a b:V4):V4:=⟨a.x0+ b.x0,a.x1+ b.x1,a.x2+ b.x2,a.x3+ b.x3⟩
def vs (s:ℂ) (a:V4):V4:=⟨s*a.x0,s*a.x1,s*a.x2,s*a.x3⟩
def oc (r:Fq) (X:Mt):V4:=⟨X (r,0),X (r,1),X (r,2),X (r,3)⟩
lemma Rb:(∀ a b c d e:V4,mp (va a b) c d e=mp a c d e+ mp b c d e)/\
  (∀ a b c d e:V4,mp c (va a b) d e=mp c a d e+ mp c b d e)/\
  (∀ a b c d e:V4,mp c d (va a b) e=mp c d a e+ mp c d b e)/\
  (∀ a b c d e:V4,mp c d e (va a b)=mp c d e a+ mp c d e b)/\
  (∀ (s:ℂ) (a c d e:V4),mp (vs s a) c d e=s*mp a c d e)/\
  (∀ (s:ℂ) (a c d e:V4),mp c (vs s a) d e=s*mp c a d e)/\
  (∀ (s:ℂ) (a c d e:V4),mp c d (vs s a) e=s*mp c d a e)/\
  (∀ (s:ℂ) (a c d e:V4),mp c d e (vs s a)=s*mp c d e a):=by
 refine⟨?_,?_,?_,?_,?_,?_,?_,?_⟩<;>intros<;>simp only[mp,va,vs]<;>ring
lemma afA (M:Mt):p4 M=mp (oc 0 M) (oc 1 M) (oc 2 M) (oc 3 M):=rfl
def u3 (a b c d:ℂ) (h:∀ x:ℂ,a+ b*x+ c*x^2+ d*x^3=0):
  a=0/\b=0/\c=0/\d=0:=by
 have h0:=h 0;have h1:=h 1;have h2:=h (-1);have e:=h 2
 exact⟨by linear_combination h0,by linear_combination (-1/2:ℂ)*h0+ h1-(1/3:ℂ)*h2-(1/6:ℂ)*e,
  by linear_combination -h0+(1/2:ℂ)*h1+(1/2:ℂ)*h2,
  by linear_combination (1/2:ℂ)*h0-(1/2:ℂ)*h1-(1/6:ℂ)*h2+(1/6:ℂ)*e⟩
def bv (a I7 b c d e f g c20 i j c23 l m n o:ℂ)
  (h:∀ x y:ℂ,(a+ I7*y+ b*y^2+ c*y^3)+(d+ e*y+ f*y^2+ g*y^3)*x+(c20+ i*y+ j*y^2+ c23*y^3)*x^2+(l+ m*y+ n*y^2+ o*y^3)*x^3=0):
  a=0/\I7=0/\b=0/\c=0/\d=0/\e=0/\f=0/\g=0/\c20=0/\i=0/\j=0/\c23=0/\l=0/\m=0/\n=0/\o=0:=by
 have k:=λy=> u3 _ _ _ _ (λx=> h x y)
 obtain⟨p,q,r,s⟩:=u3 _ _ _ _ (λy=>(k y).1)
 obtain⟨t,u,v,w⟩:=u3 _ _ _ _ (λy=>(k y).2.1)
 obtain⟨z,A,B,C⟩:=u3 _ _ _ _ (λy=>(k y).2.2.1)
 obtain⟨D,E,F,G⟩:=u3 _ _ _ _ (λy=>(k y).2.2.2)
 exact⟨p,q,r,s,t,u,v,w,z,A,B,C,D,E,F,G⟩
def agg (z y d e b c t a:V4) (h:∀ s0 s1 j k:ℂ,mp (va (va (va B0 (vs s0 z)) (vs j d)) (vs k b)) (va (va (va B1 (vs s1 y)) (vs j e)) (vs k c)) (va B2 (vs k a)) (va B3 (vs j t))=65):
  QF z y d e b c t a:=by
 obtain⟨aC,o,p,q,r,s,u,v,w,A,l,ax,m,n,ay,ai⟩:=bv ((mp B0 B1 B2 B3-65)) (mp B0 B1 a B3+ mp B0 c B2 B3+ mp b B1 B2 B3) (mp B0 c a B3+ mp b B1 a B3+ mp b c B2 B3) (mp b c a B3) (mp B0 B1 B2 t+ mp B0 e B2 B3+ mp d B1 B2 B3) (mp B0 B1 a t+ mp B0 e a B3+ mp B0 c B2 t+ mp d B1 a B3+ mp d c B2 B3+ mp b B1 B2 t+ mp b e B2 B3) (mp B0 c a t+ mp d c a B3+ mp b B1 a t+ mp b e a B3+ mp b c B2 t) (mp b c a t) (mp B0 e B2 t+ mp d B1 B2 t+ mp d e B2 B3) (mp B0 e a t+ mp d B1 a t+ mp d e a B3+ mp d c B2 t+ mp b e B2 t) (mp d c a t+ mp b e a t) 0 (mp d e B2 t) (mp d e a t) 0 0 (λx y=> by
  have f:=h 0 0 x y;simp only[Rb]at f;linear_combination f)
 obtain⟨B,C,D,aD,E,F,G,aE,H,J,W,X,Y,Z,ae,ag⟩:=bv (mp z B1 B2 B3) (mp z B1 a B3+ mp z c B2 B3) (mp z c a B3) 0 (mp z B1 B2 t+ mp z e B2 B3) (mp z B1 a t+ mp z e a B3+ mp z c B2 t) (mp z c a t) 0 (mp z e B2 t) (mp z e a t) 0 0 0 0 0 0 (λx y=> by
  have g:=h 1 0 x y;have f:=h 0 0 x y;simp only[Rb]at g f;linear_combination g- f)
 obtain⟨K,L,M,aF,N,O,P,aG,Q,R,aj,al,am,ao,ap,as⟩:=bv (mp B0 y B2 B3) (mp B0 y a B3+ mp b y B2 B3) (mp b y a B3) 0 (mp B0 y B2 t+ mp d y B2 B3) (mp B0 y a t+ mp d y a B3+ mp b y B2 t) (mp b y a t) 0 (mp d y B2 t) (mp d y a t) 0 0 0 0 0 0 (λx y=> by
  have Nu:=h 0 1 x y;have f:=h 0 0 x y;simp only[Rb]at Nu f;linear_combination Nu- f)
 obtain⟨S,T,aH,aI,U,V,aJ,aK,aL,aM,au,av,aw,az,aA,aB⟩:=bv (mp z y B2 B3) (mp z y a B3) 0 0 (mp z y B2 t) (mp z y a t) 0 0 0 0 0 0 0 0 0 0 (λx y=> by
  have i:=h 1 1 x y;have g:=h 1 0 x y;have Nu:=h 0 1 x y;have f:=h 0 0 x y;simp only[Rb]at i g Nu f;linear_combination i- g- Nu+ f)
 exact⟨o,p,q,r,s,u,v,w,A,l,m,n,K,L,M,N,O,P,Q,R,B,C,D,E,F,G,H,J,S,T,U,V⟩
def agh (z y x0 x1 a b:V4) (h:∀ P Q G H:ℂ,mp (va (va B0 (vs P z)) (vs G x0)) (va (va B1 (vs Q y)) (vs G x1)) (va B2 (vs H a)) (va B3 (vs H b))=65):
  TH z y x0 x1 a b:=by
 obtain⟨as,g,i,au,j,k,l,av,m,n,f,aj,R,S,al,T⟩:=bv ((mp B0 B1 B2 B3-65)) (mp B0 B1 B2 b+ mp B0 B1 a B3) (mp B0 B1 a b) 0 (mp B0 x1 B2 B3+ mp x0 B1 B2 B3) (mp B0 x1 B2 b+ mp B0 x1 a B3+ mp x0 B1 B2 b+ mp x0 B1 a B3) (mp B0 x1 a b+ mp x0 B1 a b) 0 (mp x0 x1 B2 B3) (mp x0 x1 B2 b+ mp x0 x1 a B3) (mp x0 x1 a b) 0 0 0 0 0 (λx y=> by
  have Lu:=h 0 0 x y;simp only[Rb]at Lu;linear_combination Lu)
 obtain⟨o,p,q,aw,r,s,t,ax,ay,az,J,K,L,M,N,O⟩:=bv (mp z B1 B2 B3) (mp z B1 B2 b+ mp z B1 a B3) (mp z B1 a b) 0 (mp z x1 B2 B3) (mp z x1 B2 b+ mp z x1 a B3) (mp z x1 a b) 0 0 0 0 0 0 0 0 0 (λx y=> by
  have c:=h 1 0 x y;have Lu:=h 0 0 x y;simp only[Rb]at c Lu;linear_combination c- Lu)
 obtain⟨u,v,w,aA,A,B,C,aB,aC,aD,U,V,W,X,Y,Z⟩:=bv (mp B0 y B2 B3) (mp B0 y B2 b+ mp B0 y a B3) (mp B0 y a b) 0 (mp x0 y B2 B3) (mp x0 y B2 b+ mp x0 y a B3) (mp x0 y a b) 0 0 0 0 0 0 0 0 0 (λx y=> by
  have d:=h 0 1 x y;have Lu:=h 0 0 x y;simp only[Rb]at d Lu;linear_combination d- Lu)
 obtain⟨D,E,F,aE,aF,aG,aH,aI,aJ,aK,ae,ag,ai,am,ao,ap⟩:=bv (mp z y B2 B3) (mp z y B2 b+ mp z y a B3) (mp z y a b) 0 0 0 0 0 0 0 0 0 0 0 0 0 (λx y=> by
  have e:=h 1 1 x y;have c:=h 1 0 x y;have d:=h 0 1 x y;have Lu:=h 0 0 x y;simp only[Rb]at e c d Lu;linear_combination e- c- d+ Lu)
 exact⟨g,i,j,k,l,m,n,f,u,v,w,A,B,C,o,p,q,r,s,t,D,E,F⟩
def SJ (a:ℂ) {R:ℂ->Prop} (h:a=0-> ∃ k,R k):∃ k,k*a=1\/k*a=0/\R k:=by
 by_cases h0:a=0
 .obtain⟨k,b⟩:=h h0
  exact⟨k,.inr ⟨by rw[h0,C3],b⟩⟩
 .exact⟨a⁻¹,.inl (G5 h0)⟩
def ch3 (a b c:ℂ) (h:¬ (a=0/\b=0/\c=0)):
  ∃ k:ℂ,k*a=1\/k*a=0/\(k*b=1\/k*b=0/\(k*c=1)):=
 SJ a λd=> SJ b λe=>⟨c⁻¹,G5 λf=> h ⟨d,e,f⟩⟩
def adx (a b c d:ℂ) (h:¬ (a=0/\b=0/\c=0/\d=0)):
  ∃ k:ℂ,k*a=1\/k*a=0/\(k*b=1\/k*b=0/\(k*c=1\/k*c=0/\(k*d=1))):=
 SJ a λe=> SJ b λf=> SJ c λg=>⟨d⁻¹,G5 λh3=> h ⟨e,f,g,h3⟩⟩
def anq (a b c d e f g h8:ℂ) (h:¬ (a=0/\b=0/\c=0/\d=0/\e=0/\f=0/\g=0/\h8=0)):
  ∃ k:ℂ,k*a=1\/k*a=0/\(k*b=1\/k*b=0/\(k*c=1\/k*c=0/\(k*d=1\/k*d=0/\(k*e=1\/k*e=0/\(k*f=1\/k*f=0/\(k*g=1\/k*g=0/\(k*h8=1))))))):=
 SJ a λh0=> SJ b λi=> SJ c λj=> SJ d λl=> SJ e λm=> SJ f λn=> SJ g λo=>
  ⟨h8⁻¹,G5 λp=> h ⟨h0,i,j,l,m,n,o,p⟩⟩
def zch (L:Sq) (n:∀ t∈L,p4 (Bm+ t)=65) (X:Mt) (d:X∈L) (h:X≠0)
  (hz:∀ i j,i≠0->X (i,j)=0):∃ Z∈L,(∀ i j,i≠0->Z (i,j)=0)/\ ∃ p:Fq,Z (0,p)=16/\
   ((p=1/\ ∃ a b,oc 0 Z=zv 1 a b)\/(p=2/\ ∃ a,oc 0 Z=zv 0 1 a)\/(p=3/\oc 0 Z=zv 0 0 1)):=by
 have F:16*X (0,0)+11*X (0,1)+11*X (0,2)+11*X (0,3)=0:=by
  have l:=n X d;simp +decide only[p4,Bm,A1,A9,A8,hz 1,hz 2,hz 3,D7,
   L8,B8,C0]at l
  grind
 obtain⟨k,o⟩:=ch3 (X (0,1)) (X (0,2)) (X (0,3)) (λ⟨e,f,g⟩=> h (by
  ext ⟨i,j⟩;simp only[N7];by_cases c:i=0
  .subst c;fin_cases j
   .show X (0,0)=0
    grind
   .exact e
   .exact f
   .exact g
  .exact hz i j c))
 refine⟨(16*k)•X,L.smul_mem _ d,λi j c=> by simp[hz i j c],?_⟩
 simp only[oc,zv,A4,A5,V4.mk.injEq];rcases o with h1 | ⟨h1,m | ⟨m,q⟩⟩
 .exact⟨1,by grind,.inl ⟨rfl,k*X (0,2),k*X (0,3),by grind⟩⟩
 .exact⟨2,by grind,.inr (.inl ⟨rfl,k*X (0,3),by grind⟩)⟩
 .exact⟨3,by grind,.inr (.inr ⟨rfl,by grind⟩)⟩
def ych (L:Sq) (n:∀ t∈L,p4 (Bm+ t)=65) (X:Mt) (d:X∈L) (h:X≠0)
  (hz:∀ i j,i≠1->X (i,j)=0):∃ Z∈L,(∀ i j,i≠1->Z (i,j)=0)/\ ∃ p:Fq,Z (1,p)=11/\
   ((p=1/\ ∃ a b,oc 1 Z=yv 1 a b)\/(p=2/\ ∃ a,oc 1 Z=yv 0 1 a)\/(p=3/\oc 1 Z=yv 0 0 1)):=by
 have F:11*X (1,0)+16*X (1,1)+11*X (1,2)+11*X (1,3)=0:=by
  have l:=n X d;simp +decide only[p4,Bm,A1,A9,A8,hz 0,hz 2,hz 3,D7,
   L8,B8,C0]at l
  grind
 obtain⟨k,o⟩:=ch3 (X (1,1)) (X (1,2)) (X (1,3)) (λ⟨e,f,g⟩=> h (by
  ext ⟨i,j⟩;simp only[N7];by_cases c:i=1
  .subst c;fin_cases j
   .show X (1,0)=0
    grind
   .exact e
   .exact f
   .exact g
  .exact hz i j c))
 refine⟨(11*k)•X,L.smul_mem _ d,λi j c=> by simp[hz i j c],?_⟩
 simp only[oc,yv,A4,A5,V4.mk.injEq];rcases o with h1 | ⟨h1,m | ⟨m,q⟩⟩
 .exact⟨1,by grind,.inl ⟨rfl,k*X (1,2),k*X (1,3),by grind⟩⟩
 .exact⟨2,by grind,.inr (.inl ⟨rfl,k*X (1,3),by grind⟩)⟩
 .exact⟨3,by grind,.inr (.inr ⟨rfl,by grind⟩)⟩
lemma lv2 (Z Y a W3:Mt) (k:∀ i j,i≠0->Z (i,j)=0) (h:∀ i j,i≠1->Y (i,j)=0)
  (f:∀ j,a (2,j)=0) (g:∀ j,W3 (3,j)=0) (d e b c:ℂ):
  p4 (Bm+(d•Z+ e•Y+ b•a+ c•W3))=mp (va (va (va B0 (vs d (oc 0 Z))) (vs b (oc 0 a))) (vs c (oc 0 W3)))
   (va (va (va B1 (vs e (oc 1 Y))) (vs b (oc 1 a))) (vs c (oc 1 W3))) (va B2 (vs c (oc 2 W3)))
   (va B3 (vs b (oc 3 a))):=by
 rw[afA];congr 1<;>simp only[oc,va,vs,B0,B1,B2,B3]<;>congr 1<;>
  simp[Bm,k,h,f,g]<;>ring
lemma lv3 (Z Y W K:Mt) (f:∀ i j,i≠0->Z (i,j)=0) (e:∀ i j,i≠1->Y (i,j)=0)
  (k:∀ j,W (2,j)=0) (l:∀ j,W (3,j)=0) (g:∀ j,K (0,j)=0) (h:∀ j,K (1,j)=0) (c d a b:ℂ):
  p4 (Bm+(c•Z+ d•Y+ a•W+ b•K))=mp (va (va B0 (vs c (oc 0 Z))) (vs a (oc 0 W)))
   (va (va B1 (vs d (oc 1 Y))) (vs a (oc 1 W))) (va B2 (vs b (oc 2 K))) (va B3 (vs b (oc 3 K))):=by
 rw[afA];congr 1<;>simp only[oc,va,vs,B0,B1,B2,B3]<;>congr 1<;>
  simp[Bm,f,e,k,l,g,h]<;>ring
def agr (Z Y d W3:Mt) (M:∀ i j,i≠0->Z (i,j)=0) (L:∀ i j,i≠1->Y (i,j)=0)
  (N:∀ j,d (2,j)=0) (O:∀ j,W3 (3,j)=0)
  (Me:∀ a b e:ℂ,∀ c,m3 2 c (a•Z+ b•Y+ e•d)=0) (MP:∀ a b e:ℂ,∀ c,m3 3 c (a•Z+ b•Y+ e•W3)=0):
  O2 (oc 0 Z) (oc 1 Y) (oc 0 d) (oc 1 d) (oc 0 W3) (oc 1 W3) (oc 3 d) (oc 2 W3):=by
 have Wu:=Me 0 0 1 0;have Ww:=Me 0 0 1 1;have k:=Me 0 0 1 2;have l:=Me 0 0 1 3;have v:=Me 1 0 1 0;have w:=Me 1 0 1 1;have x:=Me 1 0 1 2;have y:=Me 1 0 1 3;have r:=Me 0 1 1 0;have s:=Me 0 1 1 1;have t:=Me 0 1 1 2;have u:=Me 0 1 1 3;have G:=Me 1 1 1 0;have H:=Me 1 1 1 1;have J:=Me 1 1 1 2;have K:=Me 1 1 1 3;have WB:=MP 0 0 1 0;have f:=MP 0 0 1 1;have g:=MP 0 0 1 2;have h:=MP 0 0 1 3;have n:=MP 1 0 1 0;have o:=MP 1 0 1 1;have p:=MP 1 0 1 2;have q:=MP 1 0 1 3;have z:=MP 0 1 1 0;have A:=MP 0 1 1 1;have B:=MP 0 1 1 2;have m:=MP 0 1 1 3;have C:=MP 1 1 1 0;have D:=MP 1 1 1 1;have E:=MP 1 1 1 2;have F:=MP 1 1 1 3;simp +decide only[m3,PV,A1,A4,A5,Fin.isValue,
  Fin.reduceAdd,M 1,M 2,M 3,L 0,L 2,L 3,N,O,D7,L8,F4,C3,
  C0,B8,G8]at Wu Ww k l v w x y r s t u G H J K WB f g h n o p q z A B m C D E F
 simp only[O2,me,lu,mh,mj,oc]
 exact⟨by linear_combination G- v- r+ Wu,
  by linear_combination H- w- s+ Ww,
  by linear_combination J- x- t+ k,
  by linear_combination K- y- u+ l,
  by linear_combination v- Wu,
  by linear_combination w- Ww,
  by linear_combination x- k,
  by linear_combination y- l,
  by linear_combination r- Wu,
  by linear_combination s- Ww,
  by linear_combination t- k,
  by linear_combination u- l,
  by linear_combination Wu,
  by linear_combination Ww,
  by linear_combination k,
  by linear_combination l,
  by linear_combination C- n- z+ WB,
  by linear_combination D- o- A+ f,
  by linear_combination E- p- B+ g,
  by linear_combination F- q- m+ h,
  by linear_combination n- WB,
  by linear_combination o- f,
  by linear_combination p- g,
  by linear_combination q- h,
  by linear_combination z- WB,
  by linear_combination A- f,
  by linear_combination B- g,
  by linear_combination m- h,
  by linear_combination WB,
  by linear_combination f,
  by linear_combination g,
  by linear_combination h⟩
def ags (Z Y K:Mt) (d:∀ i j,i≠0->Z (i,j)=0) (hy:∀ i j,i≠1->Y (i,j)=0)
  (n:∀ j,K (0,j)=0) (o:∀ j,K (1,j)=0)
  (b:∀ c,m3 0 c (Y+ K)=0) (a:∀ c,m3 1 c (Z+ K)=0):
  Ri (oc 0 Z) (oc 1 Y) (oc 2 K) (oc 3 K):=by
 have e:=b 0;have f:=b 1;have g:=b 2;have h:=b 3;have g0:=a 0;have k:=a 1;have l:=a 2;have m:=a 3;simp +decide only[m3,PV,A1,Fin.isValue,Fin.reduceAdd,d 1,d 2,d 3,
  hy 0,hy 2,hy 3,n,o,D7,L8,C0,B8]at e f g h g0 k l m
 simp only[Ri,me,lu,mh,mj,oc]
 exact⟨by linear_combination e,by linear_combination f,by linear_combination g,by linear_combination h,by linear_combination g0,by linear_combination k,by linear_combination l,by linear_combination m⟩
def ajy (z y x0 x1 a b:V4) (h:TH z y x0 x1 a b):Yy z y x0 x1 a b:=by
 obtain⟨r,s,t,u,v,k,l,m,w,x,n,l11,j,i,o,p,q,c,d,e,f,g,l22⟩:=h
 exact⟨by linear_combination f,by linear_combination l22,by linear_combination g,by linear_combination c,by linear_combination e,by linear_combination d,by linear_combination l11,by linear_combination i,by linear_combination j,by linear_combination k,by linear_combination m,by linear_combination l⟩
def anS (a b c d e f:ℂ) (g:a*b*c=0) (h:a*d*e=0)
  (i:b*d*f=0) (j:c*e*f=0):
  (a=0/\b=0/\c=0)\/(a=0/\d=0/\e=0)\/(b=0/\d=0/\f=0)\/
  (c=0/\e=0/\f=0)\/(a=0/\f=0)\/(b=0/\e=0)\/(c=0/\d=0):=by
 simp only[A0]at g h i j;tauto
def Pz (a b:V4): Prop :=(a.x0*b.x1+ a.x1*b.x0)=0/\(a.x0*b.x2+ a.x2*b.x0)=0/\(a.x0*b.x3+ a.x3*b.x0)=0/\(a.x1*b.x2+ a.x2*b.x1)=0/\(a.x1*b.x3+ a.x3*b.x1)=0/\(a.x2*b.x3+ a.x3*b.x2)=0
def cfk (L:Sq) (p:∀ t∈L,p4 (Bm+ t)=65) (Z Y a W3:Mt) (mZ:Z∈L) (s:Y∈L)
  (h:a∈L) (mW3:W3∈L) (r:∀ i j,i≠0->Z (i,j)=0) (q:∀ i j,i≠1->Y (i,j)=0)
  (n:∀ j,a (2,j)=0) (o:∀ j,W3 (3,j)=0) (c:Fq):
  Z (0,c)*Y (1,c)*a (3,c)*W3 (2,c)=0:=by
 by_contra b;have x:=F9 b;have w:=F9 (D2 b);have v:=F9 (D2 (D2 b));have u:=D2 (D2 (D2 b));apply LZ (L.map Mv) (QR L p) c;have f:=Ml L c Z mZ;rw[NM 0 c Z r]at f;have d:=Ir _ _ _ u f;have g:=Ml L c Y s;rw[NM 1 c Y q]at g;have e:=Ir _ _ _ v g
 have m:(single 3 (1:ℂ):Fq->ℂ)∈(L.map Mv).map (af c):=by
  apply Ir _ _ _ w
  have hv:a (3,c)•(single 3 (1:ℂ):Fq->ℂ)=(λi=> a (i,c))- a (0,c)•single 0 (1:ℂ)
    - a (1,c)•single 1 (1:ℂ):=by
   ext i;fin_cases i<;>simp[C1,n]
  rw[hv];exact F8 _ (F8 _ (Ml L c a h) (D6 _ _ d))
   (D6 _ _ e)
 have l:(single 2 (1:ℂ):Fq->ℂ)∈(L.map Mv).map (af c):=by
  apply Ir _ _ _ x
  have hv:W3 (2,c)•(single 2 (1:ℂ):Fq->ℂ)=(λi=> W3 (i,c))- W3 (0,c)•single 0 (1:ℂ)
    - W3 (1,c)•single 1 (1:ℂ):=by
   ext i;fin_cases i<;>simp[C1,o]
  rw[hv];exact F8 _ (F8 _ (Ml L c W3 mW3) (D6 _ _ d))
   (D6 _ _ e)
 apply M5;intro k;fin_cases k
 .exact d
 .exact e
 .exact l
 .exact m
def nrm (W Z Y:Mt) (b:∀ i j,i≠0->Z (i,j)=0) (a:∀ i j,i≠1->Y (i,j)=0) (p q:Fq)
  (e:Z (0,p)=16) (f:Y (1,q)=11):∃ V:Mt,V=W-(W (0,p)/16)•Z-(W (1,q)/11)•Y/\
  V (0,p)=0/\V (1,q)=0/\ ∀ i j,i≠0->i≠1->V (i,j)=W (i,j):=by
 refine⟨_,rfl,?_,?_,λi j c d=> ?_⟩
 .simp only[G3,A4,A5,e,a 0 p (by decide)];ring
 .simp only[G3,A4,A5,f,b 1 q (by decide)];ring
 .simp only[G3,A4,A5,b i j c,a i j d];ring
def NZ (b:V4): Prop := ¬ (b.x0=0/\b.x1=0/\b.x2=0/\b.x3=0)
def abX: Prop := ∀ z y c d e f t t2:V4,Iw z y c d e f t t2->
 ((∃ a b,z=zv 1 a b)/\c.x1=0/\e.x1=0\/(∃ a,z=zv 0 1 a)/\c.x2=0/\e.x2=0\/
  z=zv 0 0 1/\c.x3=0/\e.x3=0)->
 ((∃ a b,y=yv 1 a b)/\d.x1=0/\f.x1=0\/(∃ a,y=yv 0 1 a)/\d.x2=0/\f.x2=0\/
  y=yv 0 0 1/\d.x3=0/\f.x3=0)->
 (t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1)))->
 (t2.x0=1\/t2.x0=0/\(t2.x1=1\/t2.x1=0/\(t2.x2=1\/t2.x2=0/\t2.x3=1)))->NZ c\/NZ d->False
def XC (x0 x1:V4): Prop :=x0.x0=1\/x0.x0=0/\(x0.x1=1\/x0.x1=0/\(x0.x2=1\/x0.x2=0/\(x0.x3=1\/
 x0.x3=0/\(x1.x0=1\/x1.x0=0/\(x1.x1=1\/x1.x1=0/\(x1.x2=1\/x1.x2=0/\x1.x3=1))))))
def AC (a:V4): Prop :=a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1))
def abY: Prop := ∀ z y x0 x1 a b:V4,Mh z y x0 x1 a b->
 ((∃ c d,z=zv 1 c d)/\x0.x1=0\/(∃ c,z=zv 0 1 c)/\x0.x2=0\/z=zv 0 0 1/\x0.x3=0)->
 ((∃ c d,y=yv 1 c d)/\x1.x1=0\/(∃ c,y=yv 0 1 c)/\x1.x2=0\/y=yv 0 0 1/\x1.x3=0)->
 XC x0 x1->AC a->NZ b->False
def agU (k2:abX) (k3:abY):RE:=by
 intro L hL P t u v n2 n3;obtain⟨X0,aw,aA,aD⟩:=u;obtain⟨X1,ax,aB,aE⟩:=v;obtain⟨Z,l,f,pz,B,cz⟩:=zch L hL X0 aw aA aD;obtain⟨Y,k,d,py,A,cy⟩:=ych L hL X1 ax aB aE;by_cases hk:Ar L 2≤ Ar L 3
 .classical
  have A2:=MF L P 2 (t 2)
  have av:¬ Ar L 2≤ span ℂ ({Z,Y}:Set Mt):=λh=> by
   have h2:finrank ℂ (span ℂ ({Z,Y}:Set Mt))≤2:=by
    have :=finrank_span_finset_le_card (R:= ℂ) ({Z,Y}:Finset Mt);simp only[Finset.coe_insert,Finset.coe_singleton]at this;exact this.trans Finset.card_le_two
   have h1:=(E7 h).trans h2;omega
  obtain⟨X,Q,nX⟩:=N8.1 av;rw[SetLike.mem_coe,ei]at Q;have x3:∀ j,X (3,j)=0:=((ei L 3 X).1 (hk ((ei L 2 X).2 Q))).2;obtain⟨V,hV,a0,b0,r⟩:=nrm X Z Y f d pz py B A
  have mV:V∈L:=by rw[hV];exact L.sub_mem (L.sub_mem Q.1 (L.smul_mem _ l)) (L.smul_mem _ k)
  have G:∀ j,V (2,j)=0:=λj=> by rw[r 2 j (by decide) (by decide)];exact Q.2 j
  have H:∀ j,V (3,j)=0:=λj=> by rw[r 3 j (by decide) (by decide)];exact x3 j
  obtain⟨m,au⟩:=anq (V (0,0)) (V (0,1)) (V (0,2)) (V (0,3)) (V (1,0)) (V (1,1)) (V (1,2)) (V (1,3))
   (λ⟨o,p,e2,s,e4,e5,e6,e7⟩=> nX (by
    have ao:V=0:=by
     ext ⟨i,j⟩;simp only[N7];fin_cases i<;>fin_cases j;exacts [o,p,e2,s,e4,e5,e6,e7,G 0,G 1,G 2,G 3,H 0,H 1,H 2,H 3]
    rw[ao,sub_sub,eq_comm,sub_eq_zero]at hV;rw[hV]
    exact Submodule.add_mem _ (D6 _ _ (P9 (by simp)))
     (D6 _ _ (P9 (by simp)))))
  obtain⟨K0,ai,az,k00,ae⟩:=Zv L hL P 0 1 (by decide)
  obtain⟨ka,W⟩:=adx (K0 (2,0)) (K0 (2,1)) (K0 (2,2)) (K0 (2,3)) (λ⟨o,p,e2,s⟩=>
   n3 ⟨K0,ai,az,λi j hi=> by
    fin_cases i
    .exact k00 j
    .exact ae j
    .fin_cases j;exacts [o,p,e2,s]
    .exact absurd rfl hi⟩)
  have ay:m•V∈L:=L.smul_mem _ mV;have S:ka•K0∈L:=L.smul_mem _ ai
  have w2:∀ j,(m•V) (2,j)=0:=λj=> by simp[G j]
  have w3:∀ j,(m•V) (3,j)=0:=λj=> by simp[H j]
  have T:∀ j,(ka•K0) (0,j)=0:=λj=> by simp[k00 j]
  have U:∀ j,(ka•K0) (1,j)=0:=λj=> by simp[ae j]
  have hb:NZ (oc 3 (ka•K0)):=by
   rintro⟨o,p,e2,s⟩
   refine n2 ⟨ka•K0,S,λh0=> ?_,λi j hi=> ?_⟩
   .have z:∀ j,ka*K0 (2,j)=0:=λj=> by simpa using congrFun h0 (2,j)
    rcases W with h | ⟨-,h | ⟨-,h | ⟨-,h⟩⟩⟩<;>rw[z]at h<;>exact G9 h
   .fin_cases i
    .exact T j
    .exact U j
    .exact absurd rfl hi
    .fin_cases j;exacts [o,p,e2,s]
  have hl:=agh (oc 0 Z) (oc 1 Y) (oc 0 (m•V)) (oc 1 (m•V)) (oc 2 (ka•K0)) (oc 3 (ka•K0))
   (λu v E F=> by
    rw[<- lv3 Z Y (m•V) (ka•K0) f d w2 w3 T U];exact hL _ (L.add_mem (L.add_mem (L.add_mem (L.smul_mem _ l) (L.smul_mem _ k)) (L.smul_mem _ ay))
     (L.smul_mem _ S)))
  refine k3 _ _ _ _ _ _ ⟨hl,ags Z Y (ka•K0) f d T U (λc=> VE L hL 0 (t 0) _ (L.add_mem k S)
   (λj=> by simp[d 0 j (by decide),T j]) c) (λc=> VE L hL 1 (t 1) _ (L.add_mem l S)
   (λj=> by simp[f 1 j (by decide),U j]) c),ajy _ _ _ _ _ _ hl⟩ ?_ ?_ ?_ ?_ hb
  .have q:=Q0 m a0;rcases cz with⟨rfl,e⟩ | ⟨rfl,e⟩ | ⟨rfl,e⟩;exacts [.inl ⟨e,q⟩,.inr (.inl ⟨e,q⟩),.inr (.inr ⟨e,q⟩)]
  .have q:=Q0 m b0;rcases cy with⟨rfl,e⟩ | ⟨rfl,e⟩ | ⟨rfl,e⟩;exacts [.inl ⟨e,q⟩,.inr (.inl ⟨e,q⟩),.inr (.inr ⟨e,q⟩)]
  .simpa only[XC,oc,A4,A5] using au
  .simpa only[AC,oc,A4,A5] using W
 have A2:=MF L P 2 (t 2);have A3:=MF L P 3 (t 3);obtain⟨n,w,aj⟩:=N8.1 hk
 have SY:¬ Ar L 3≤ Ar L 2:=λh=> hk (M3 h (by rw[A3,A2])).ge
 obtain⟨W3,x,al⟩:=N8.1 SY;rw[SetLike.mem_coe,ei]at w x aj al
 obtain⟨k2',LR⟩:=adx (n (3,0)) (n (3,1)) (n (3,2)) (n (3,3)) (λ⟨o,p,e2,s⟩=>
  aj ⟨w.1,λj=> by fin_cases j<;>assumption⟩)
 obtain⟨ag,Nz⟩:=adx (W3 (2,0)) (W3 (2,1)) (W3 (2,2)) (W3 (2,3)) (λ⟨o,p,e2,s⟩=>
  al ⟨x.1,λj=> by fin_cases j<;>assumption⟩)
 obtain⟨V2,ap,K,N,r2⟩:=nrm (k2'•n) Z Y f d pz py B A;obtain⟨g,as,M,O,r3⟩:=nrm (ag•W3) Z Y f d pz py B A
 have y:V2∈L:=by
  rw[ap];exact L.sub_mem (L.sub_mem (L.smul_mem _ w.1) (L.smul_mem _ l)) (L.smul_mem _ k)
 have D:g∈L:=by
  rw[as];exact L.sub_mem (L.sub_mem (L.smul_mem _ x.1) (L.smul_mem _ l)) (L.smul_mem _ k)
 have J:∀ j,V2 (2,j)=0:=λj=> by
  rw[r2 2 j (by decide) (by decide)];simp[w.2 j]
 have z3:∀ j,g (3,j)=0:=λj=> by
  rw[r3 3 j (by decide) (by decide)];simp[x.2 j]
 have am:∀ j,V2 (3,j)=k2'*n (3,j):=λj=> by
  rw[r2 3 j (by decide) (by decide)];simp
 have aC:∀ j,g (2,j)=ag*W3 (2,j):=λj=> by
  rw[r3 2 j (by decide) (by decide)];simp
 have mem:∀ u v E F:ℂ,u•Z+ v•Y+ E•V2+ F•g∈L:=λu v E F=>
  L.add_mem (L.add_mem (L.add_mem (L.smul_mem _ l) (L.smul_mem _ k)) (L.smul_mem _ y)) (L.smul_mem _ D)
 have C:=cfk L hL Z Y V2 g l k y D f d J z3
 have hG:Iw (oc 0 Z) (oc 1 Y) (oc 0 V2) (oc 1 V2) (oc 0 g) (oc 1 g) (oc 3 V2) (oc 2 g):=by
  refine⟨agg _ _ _ _ _ _ _ _ (λu v E F=> ?_),agr Z Y V2 g f d J z3 (λa b e c=> ?_)
   (λa b e c=> ?_),C 0,C 1,
   C 2,C 3⟩
  .rw[<- lv2 Z Y V2 g f d J z3];exact hL _ (mem u v E F)
  .exact VE L hL 2 (t 2) _ (L.add_mem (L.add_mem (L.smul_mem _ l) (L.smul_mem _ k)) (L.smul_mem _ y))
    (λj=> by simp[f 2 j (by decide),d 2 j (by decide),J j]) c
  .exact VE L hL 3 (t 3) _ (L.add_mem (L.add_mem (L.smul_mem _ l) (L.smul_mem _ k)) (L.smul_mem _ D))
    (λj=> by simp[f 3 j (by decide),d 3 j (by decide),z3 j]) c
 refine k2 _ _ _ _ _ _ _ _ hG ?_ ?_ ?_ ?_ ?_
 .rcases cz with⟨rfl,e⟩ | ⟨rfl,e⟩ | ⟨rfl,e⟩;exacts [.inl ⟨e,K,M⟩,.inr (.inl ⟨e,K,M⟩),.inr (.inr ⟨e,K,M⟩)]
 .rcases cy with⟨rfl,e⟩ | ⟨rfl,e⟩ | ⟨rfl,e⟩;exacts [.inl ⟨e,N,O⟩,.inr (.inl ⟨e,N,O⟩),.inr (.inr ⟨e,N,O⟩)]
 .simp only[oc,am];exact LR
 .simp only[oc,aC];exact Nz
 .by_contra hc;simp only[not_or,NZ,not_not,oc]at hc;obtain⟨⟨a0,a1,K,M⟩,b0,b1,N,O⟩:=hc
  refine n3 ⟨V2,y,λh0=> ?_,λi j hi=> ?_⟩
  .have e:∀ j,k2'*n (3,j)=0:=λj=> by simpa[h0] using (am j).symm
   rcases LR with h | ⟨-,h | ⟨-,h | ⟨-,h⟩⟩⟩<;>simp[e]at h
  .fin_cases i<;>fin_cases j<;>first | exact absurd rfl hi | assumption | exact J _
def abH (e f g t3 d i j k a b c w x y:ℂ)
  (l:y*e+ c*g+ b*t3=0) (s:y*d+ c*j+ b*k=0)
  (m:x*e+ c*f+ a*t3=0) (oj:x*d+ c*i+ a*k=0)
  (n:w*e+ b*f+ a*g=0) (t:w*d+ b*i+ a*j=0)
  (z:¬ (d*f- i*e=0/\d*g- j*e=0/\d*t3- k*e=0/\i*g- j*f=0/\
   i*t3- k*f=0/\j*t3- k*g=0)):a*b*c=0:=by
 by_contra h;have o:2*(a*b*c)≠0:=mul_ne_zero G0 h
 have p:d*f- i*e=0:=(A0.1 (show 2*(a*b*c)*(d*f- i*e)=0 by
  linear_combination (-a^2*d)*l+(a*b*d)*m+(a*c*d)*n+(a^2*e)*s+(-a*b*e)*oj+(-a*c*e)*t)).resolve_left o
 have q:d*g- j*e=0:=(A0.1 (show 2*(a*b*c)*(d*g- j*e)=0 by
  linear_combination (a*b*d)*l+(-b^2*d)*m+(b*c*d)*n+(-a*b*e)*s+(b^2*e)*oj+(-b*c*e)*t)).resolve_left o
 have r:d*t3- k*e=0:=(A0.1 (show 2*(a*b*c)*(d*t3- k*e)=0 by
  linear_combination (a*c*d)*l+(b*c*d)*m+(-c^2*d)*n+(-a*c*e)*s+(-b*c*e)*oj+(c^2*e)*t)).resolve_left o
 by_cases u:d=0
 .by_cases v:e=0
  .subst u v
   have A:f=0:=(A0.1 (show 2*(a*b*c)*f=0 by
    linear_combination (-a^2)*l+(a*b)*m+(a*c)*n)).resolve_left o
   have B:g=0:=(A0.1 (show 2*(a*b*c)*g=0 by
    linear_combination (a*b)*l+(-b^2)*m+(b*c)*n)).resolve_left o
   have z3:t3=0:=(A0.1 (show 2*(a*b*c)*t3=0 by
    linear_combination (a*c)*l+(b*c)*m+(-c^2)*n)).resolve_left o
   subst A B z3
   exact z ⟨by ring,by ring,by ring,by ring,by ring,by ring⟩
  .exact z ⟨p,q,r,(A0.1 (show e*(i*g- j*f)=0 by linear_combination f*q- g*p)).resolve_left v,
    (A0.1 (show e*(i*t3- k*f)=0 by linear_combination f*r- t3*p)).resolve_left v,
    (A0.1 (show e*(j*t3- k*g)=0 by linear_combination g*r- t3*q)).resolve_left v⟩
 .exact z ⟨p,q,r,(A0.1 (show d*(i*g- j*f)=0 by linear_combination i*q- j*p)).resolve_left u,
   (A0.1 (show d*(i*t3- k*f)=0 by linear_combination i*r- k*p)).resolve_left u,
   (A0.1 (show d*(j*t3- k*g)=0 by linear_combination j*r- k*q)).resolve_left u⟩
def Rc (z y x A p q t s:V4) (h:O2 z y x A p q t s)
  (o:¬ (s.x0*t.x1- s.x1*t.x0=0/\s.x0*t.x2- s.x2*t.x0=0/\s.x0*t.x3- s.x3*t.x0=0/\s.x1*t.x2- s.x2*t.x1=0/\s.x1*t.x3- s.x3*t.x1=0/\s.x2*t.x3- s.x3*t.x2=0)):
  ((z.x0*y.x1+ z.x1*y.x0)=0/\(z.x0*y.x2+ z.x2*y.x0)=0/\(z.x0*y.x3+ z.x3*y.x0)=0)\/
  ((z.x0*y.x1+ z.x1*y.x0)=0/\(z.x1*y.x2+ z.x2*y.x1)=0/\(z.x1*y.x3+ z.x3*y.x1)=0)\/
  ((z.x0*y.x2+ z.x2*y.x0)=0/\(z.x1*y.x2+ z.x2*y.x1)=0/\(z.x2*y.x3+ z.x3*y.x2)=0)\/
  ((z.x0*y.x3+ z.x3*y.x0)=0/\(z.x1*y.x3+ z.x3*y.x1)=0/\(z.x2*y.x3+ z.x3*y.x2)=0)\/
  ((z.x0*y.x1+ z.x1*y.x0)=0/\(z.x2*y.x3+ z.x3*y.x2)=0)\/
  ((z.x0*y.x2+ z.x2*y.x0)=0/\(z.x1*y.x3+ z.x3*y.x1)=0)\/
  ((z.x0*y.x3+ z.x3*y.x0)=0/\(z.x1*y.x2+ z.x2*y.x1)=0):=by
 obtain⟨g,c1,i,j,-,-,-,-,-,-,-,-,-,-,-,-,k,l,m,n,-⟩:=h;simp only[me,lu,mh,mj]at g c1 i j k l m n;have r:=abH (t.x0) (t.x1) (t.x2) (t.x3) (s.x0) (s.x1) (s.x2) (s.x3) (z.x0*y.x1+ z.x1*y.x0) (z.x0*y.x2+ z.x2*y.x0) (z.x0*y.x3+ z.x3*y.x0) (z.x1*y.x2+ z.x2*y.x1) (z.x1*y.x3+ z.x3*y.x1) (z.x2*y.x3+ z.x3*y.x2)
  (by linear_combination c1) (by linear_combination l) (by linear_combination i) (by linear_combination m) (by linear_combination j) (by linear_combination n)
  (λ⟨a,b,c,d,e,f⟩=> o ⟨by linear_combination a,by linear_combination b,by linear_combination c,by linear_combination d,by linear_combination e,by linear_combination f⟩)
 have u:=abH (t.x1) (t.x0) (t.x2) (t.x3) (s.x1) (s.x0) (s.x2) (s.x3) (z.x0*y.x1+ z.x1*y.x0) (z.x1*y.x2+ z.x2*y.x1) (z.x1*y.x3+ z.x3*y.x1) (z.x0*y.x2+ z.x2*y.x0) (z.x0*y.x3+ z.x3*y.x0) (z.x2*y.x3+ z.x3*y.x2)
  (by linear_combination g) (by linear_combination k) (by linear_combination i) (by linear_combination m) (by linear_combination j) (by linear_combination n)
  (λ⟨a,b,c,d,e,f⟩=> o ⟨by linear_combination -a,by linear_combination d,by linear_combination e,by linear_combination b,by linear_combination c,by linear_combination f⟩)
 have v:=abH (t.x2) (t.x0) (t.x1) (t.x3) (s.x2) (s.x0) (s.x1) (s.x3) (z.x0*y.x2+ z.x2*y.x0) (z.x1*y.x2+ z.x2*y.x1) (z.x2*y.x3+ z.x3*y.x2) (z.x0*y.x1+ z.x1*y.x0) (z.x0*y.x3+ z.x3*y.x0) (z.x1*y.x3+ z.x3*y.x1)
  (by linear_combination g) (by linear_combination k) (by linear_combination c1) (by linear_combination l) (by linear_combination j) (by linear_combination n)
  (λ⟨a,b,c,d,e,f⟩=> o ⟨by linear_combination d,by linear_combination -a,by linear_combination e,by linear_combination -b,by linear_combination f,by linear_combination c⟩)
 have w:=abH (t.x3) (t.x0) (t.x1) (t.x2) (s.x3) (s.x0) (s.x1) (s.x2) (z.x0*y.x3+ z.x3*y.x0) (z.x1*y.x3+ z.x3*y.x1) (z.x2*y.x3+ z.x3*y.x2) (z.x0*y.x1+ z.x1*y.x0) (z.x0*y.x2+ z.x2*y.x0) (z.x1*y.x2+ z.x2*y.x1)
  (by linear_combination g) (by linear_combination k) (by linear_combination c1) (by linear_combination l) (by linear_combination i) (by linear_combination m)
  (λ⟨a,b,c,d,e,f⟩=> o ⟨by linear_combination d,by linear_combination e,by linear_combination -a,by linear_combination f,by linear_combination -b,by linear_combination -c⟩)
 exact anS _ _ _ _ _ _ (by linear_combination r) (by linear_combination u) (by linear_combination v) (by linear_combination w)
set_option maxHeartbeats 0 in
def ajG {B y ya l p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 Q S T R X Y:ℂ} (h:Iw (zv 1 B y) (yv 1 ya l) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨1,Q,S,T⟩) (⟨1,R,X,Y⟩)) (hn:NZ ⟨p0,0,p2,p3⟩\/NZ ⟨r0,0,r2,r3⟩):False:=by
 by_cases he:Q=R/\S=X/\T=Y
 .obtain⟨e,d,e2⟩:=he;subst R X Y;obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,Z,ae,ag,ai,aj,al,am,-,K,N,L,r,M,G,H,n,z,E,U⟩,⟨ao,F,s,t,O,ap,C,D,as,au,V,W,-,-,-,-,P,u,g,c51,av,aw,v,c55,ax,ay,az,aA,-⟩,⟨f,j,o,p⟩⟩:=h;simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
  rcases hn with hn | hn
  .by_cases x:p0=0
   .subst x;clear * - V W j hn;simp only[NZ]at hn;grind
   .by_cases a:Q=0<;>by_cases b:S=0<;>by_cases c:T=0<;>first | (clear * - j x a b c;grind) | (clear * - n z s t f x a b c;grind) | (clear * - P g c51 o p x a b c;grind) | (clear * - r G H u g c51 v c55 p x a b c;grind) | (clear * - r C D u g c51 v c55 o x a b c;grind)
  .by_cases x:r0=0
   .subst x;clear * - C D j hn;simp only[NZ]at hn;grind
   .by_cases a:Q=0<;>by_cases b:S=0<;>by_cases c:T=0<;>first | (clear * - j x a b c;grind) | (clear * - n z s t f x a b c;grind) | (clear * - P g c51 o p x a b c;grind) | (clear * - r G H u g c51 v c55 p x a b c;grind) | (clear * - r C D u g c51 v c55 o x a b c;grind)
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (λ⟨k0,k1,k2,k3,k4,k5⟩=> he ⟨by dsimp only at k0;linear_combination k0,by dsimp only at k1;linear_combination k1,by dsimp only at k2;linear_combination k2⟩) with⟨k,m,A⟩ | ⟨k,m,A⟩ | ⟨k,m,A⟩ | ⟨k,m,A⟩ | ⟨k,m⟩ | ⟨k,m⟩ | ⟨k,m⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,Z,ae,ag,ai,aj,al,am,-,K,N,L,r,M,G,H,n,z,E,U⟩,⟨ao,F,s,t,O,ap,C,D,as,au,V,W,-,-,-,-,P,u,g,c51,av,aw,v,c55,ax,ay,az,aA,-⟩,⟨f,j,o,p⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - g c51 k m A;grind
 .clear * - f k m A;grind
 .by_cases w:ya=0
  .have e:ya=0:=by clear * - k m A w;grind
   have d:ya+ B=0:=by clear * - k m A w;grind
   have J:0=ya:=by linear_combination -e
   subst J
   have s1:0=B:=by linear_combination -d
   subst s1;by_cases a:S=0<;>by_cases b:X=0<;>by_cases c:Q=0<;>by_cases i:R=0<;>first | (clear * - u g c51 e d a b c i;grind) | (clear * - j e d a b c i;grind) | (clear * - F s t e d a b c i;grind) | (clear * - c0 c3 Z ae ag ai aj al am K N L r M G H n z E U ao F s t O ap C D as au V W P u g c51 av aw v c55 ax ay az aA f j o p e d a b c i;grind)
  .have e:297*ya+55*l+135=0:=by clear * - k m A w;grind
   have d: -l+ y=0:=by clear * - k m A w;grind
   have e2:ya+ B=0:=by clear * - k m A w;grind
   have J:y=l:=by linear_combination d
   subst J
   have s1: -B=ya:=by linear_combination -e2
   subst s1;clear * - g f e d e2;grind
 .by_cases w:l=0
  .have e:l=0:=by clear * - k m A w;grind
   have d:l+ y=0:=by clear * - k m A w;grind
   have J:0=l:=by linear_combination -e
   subst J
   have s1:0=y:=by linear_combination -d
   subst s1;by_cases a:T=0<;>by_cases b:Y=0<;>by_cases c:Q=0<;>by_cases i:R=0<;>first | (clear * - u g c51 e d a b c i;grind) | (clear * - j e d a b c i;grind) | (clear * - F s t e d a b c i;grind) | (clear * - n z E f o e d a b c i;grind) | (clear * - c0 c3 Z ae ag ai aj al am K N L r M G H n z E U ao F s t O ap C D as au V W P u g c51 av aw v c55 ax ay az aA f j o p e d a b c i;grind)
  .have e:55*ya+297*l+135=0:=by clear * - k m A w;grind
   have d:l+ y=0:=by clear * - k m A w;grind
   have e2:297*l+55*B+135=0:=by clear * - k m A w;grind
   have J: -y=l:=by linear_combination -d
   subst J;clear * - c51 f e d e2;grind
 .clear * - g c51 f k;grind
 .have e: -121*ya*l+297*ya*B+121*ya+176*l*B+256*B=0:=by clear * - k m ;grind
  have d:l+ y=0:=by clear * - k m ;grind
  have J: -y=l:=by linear_combination -d
  subst J;by_cases a:(S-X)=0<;>by_cases b:Q=0<;>by_cases c:T=0<;>by_cases i:R=0<;>by_cases q:Y=0<;>first | (clear * - F t u c51 e d a b c i q;grind) | (clear * - j e d a b c i q;grind) | (clear * - g c51 f e d a b c i q;grind) | (clear * - g c51 p e d a b c i q;grind) | (clear * - n s t e d a b c i q;grind) | (clear * - s t f e d a b c i q;grind) | (clear * - N r M n z C D f e d a b c i q;grind) | (clear * - K N L r M n z E F s t O C D u g c51 v c55 f j p e d a b c i q;grind)
 .have e: -121*ya*l+176*ya*y+297*l*y+121*l+256*y=0:=by clear * - k m ;grind
  have d:ya+ B=0:=by clear * - k m ;grind
  have J: -B=ya:=by linear_combination -d
  subst J;by_cases a:(T-Y)=0<;>by_cases b:Q=0<;>by_cases c:S=0<;>by_cases i:R=0<;>by_cases q:X=0<;>first | (clear * - F s u g e d a b c i q;grind) | (clear * - j e d a b c i q;grind) | (clear * - g c51 f e d a b c i q;grind) | (clear * - g c51 o e d a b c i q;grind) | (clear * - s t f e d a b c i q;grind) | (clear * - n z E U e d a b c i q;grind) | (clear * - r G H n E v c55 f e d a b c i q;grind) | (by_cases f0:(1+B+y)=0<;>by_cases f1:(16-11*B+11*l)=0<;>by_cases f2:y=0<;>by_cases f3:l=0<;>first | (clear * - f j o p e d a b c i q f0 f1 f2 f3;simp only[A0,B7,A7,B4,B5]at f j o p<;>grind) | (clear * - K L r M G H n g c51 v c55 f e d a b c i q f0 f1 f2 f3;grind)) | (by_cases f0:(1+B+y)=0<;>by_cases f1:(16-11*B+11*l)=0<;>by_cases f2:y=0<;>by_cases f3:l=0<;>first | (clear * - f j o p e d a b c i q f0 f1 f2 f3;simp only[A0,B7,A7,B4,B5]at f j o p<;>grind) | (clear * - K L r n z E O C D v c55 f e d a b c i q f0 f1 f2 f3;grind))
def ajK {G q u o p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 N O M:ℂ} (h:Iw (zv 1 G q) (yv 1 u o) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨0,1,N,O⟩) (⟨0,0,1,M⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨m,n,t⟩ | ⟨m,n,t⟩ | ⟨m,n,t⟩ | ⟨m,n,t⟩ | ⟨m,n⟩ | ⟨m,n⟩ | ⟨m,n⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,P,Q,R,S,T,U,V,-,v,c22,x,y,H,J,K,c28,i,l,r⟩,⟨W,X,Y,L,C,D,Z,ae,ag,ai,aj,al,-,-,-,-,p,E,am,s,ao,ap,as,F,au,av,aw,ax,-⟩,⟨j,k,a,b⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .by_cases w:(11*u+11*o+16)=0
  .have d:11*u+11*o+16=0:=by clear * - m n t w;grind
   have c:176*u+176*o+121*G+121*q+377=0:=by clear * - m n t w;grind
   by_cases e:N=0<;>by_cases f:O=0<;>by_cases g:M=0<;>first | (clear * - j k a b d c e f g;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - c28 l d c e f g;grind) | (clear * - c28 i l d c e f g;grind) | (clear * - c28 i a d c e f g;grind) | (clear * - c28 a b d c e f g;grind) | (by_cases z:q=0<;>by_cases A:o=0<;>first | (clear * - j k a b d c e f g z A;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - v c22 x y H J K c28 i l d c e f g z A;grind)) | (by_cases z:q=0<;>by_cases A:o=0<;>first | (clear * - j k a b d c e f g z A;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - v c22 x y c28 i l C D F b d c e f g z A;grind)) | (by_cases z:q=0<;>by_cases A:o=0<;>first | (clear * - j k a b d c e f g z A;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - v c22 x y c28 i l C D F a d c e f g z A;grind))
  .have d:297*u+297*o+377=0:=by clear * - m n t w;grind
   have c: -o+ q=0:=by clear * - m n t w;grind
   have B:176*u+176*o+121*G+121*q+377=0:=by clear * - m n t w;grind
   have s0:q=o:=by linear_combination c
   subst s0;by_cases e:N=0<;>by_cases f:O=0<;>by_cases g:M=0<;>first | (clear * - j k a b d c B e f g;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - p a d c B e f g;grind) | (clear * - c28 i d c B e f g;grind) | (clear * - i l d c B e f g;grind) | (clear * - p b d c B e f g;grind) | (clear * - a b d c B e f g;grind) | (clear * - c0 c3 P Q R S T U V v c22 x y H J K c28 i l r W X Y L C D Z ae ag ai aj al p E am s ao ap as F au av aw ax j k a b d c B e f g;grind)
 .clear * - c28 i l r a b m n;grind
 .clear * - p E s m n;grind
 .clear * - c28 i l r s t;grind
 .clear * - c28 i l r m n;grind
 .have d: -121*u*o+297*u*G+121*u+176*o*G+256*G=0:=by clear * - m n ;grind
  have c:o+ q=0:=by clear * - m n ;grind
  have s0: -q=o:=by linear_combination -c
  subst s0;by_cases e:N=0<;>by_cases f:O=0<;>by_cases g:M=0<;>first | (clear * - j k a b d c e f g;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - p E s d c e f g;grind) | (clear * - c28 i l d c e f g;grind) | (clear * - c28 i a d c e f g;grind) | (clear * - c28 i l r d c e f g;grind) | (clear * - c0 c3 P Q R S T U V v c22 x y H J K c28 i l r W X Y L C D Z ae ag ai aj al p E am s ao ap as F au av aw ax j k a b d c e f g;grind)
 .clear * - L p s m n;grind
set_option maxHeartbeats 0 in
def ajL {S zb F l p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 R N O P:ℂ} (h:Iw (zv 1 S zb) (yv 1 F l) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨0,0,1,R⟩) (⟨1,N,O,P⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨i,j,v⟩ | ⟨i,j,v⟩ | ⟨i,j,v⟩ | ⟨i,j,v⟩ | ⟨i,j⟩ | ⟨i,j⟩ | ⟨i,j⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,T,U,V,W,X,Y,Z,-,y,z,A,B,J,C,D,g,n,x,E⟩,⟨o,k,ae,t,ag,ai,aj,al,am,ao,ap,as,-,-,-,-,K,u,q,p,au,av,L,M,aw,ax,ay,az,-⟩,⟨r,s,c66,m⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - q p i j v;grind
 .clear * - g n k q p c66 m i j;grind
 .clear * - o k t i j;grind
 .by_cases w:l=0
  .have b:l=0:=by clear * - i j v w;grind
   have a:l+ zb=0:=by clear * - i j v w;grind
   have Q:0=l:=by linear_combination -b
   subst Q
   have s1:0=zb:=by linear_combination -a
   subst s1;by_cases c:R=0<;>by_cases d:P=0<;>by_cases e:N=0<;>by_cases f:O=0<;>first | (clear * - r s c66 m b a c d e f;simp only[A0,B7,A7,B4,B5]at r s c66 m<;>grind) | (clear * - u q p b a c d e f;grind) | (clear * - o k t b a c d e f;grind) | (clear * - g n x b a c d e f;grind) | (clear * - g x c66 b a c d e f;grind) | (clear * - c0 c3 T U V W X Y Z y z A B J C D g n x E o k ae t ag ai aj al am ao ap as K u q p au av L M aw ax ay az r s c66 m b a c d e f;grind)
  .have b:55*F+297*l+135=0:=by clear * - i j v w;grind
   have a:l+ zb=0:=by clear * - i j v w;grind
   have e2:297*l+55*S+135=0:=by clear * - i j v w;grind
   have Q: -zb=l:=by linear_combination -a
   subst Q;clear * - y z A B C D g n o t L M c66 b a e2;grind
 .have b: -176*F*l+121*F*zb-176*l^2-121*l*zb-377*l=0:=by clear * - i j ;grind
  have a:176*F+176*l+121*S+121*zb+377=0:=by clear * - i j ;grind
  by_cases c:R=0<;>by_cases d:N=0<;>by_cases e:O=0<;>by_cases f:P=0<;>first | (clear * - r s c66 m b a c d e f;simp only[A0,B7,A7,B4,B5]at r s c66 m<;>grind) | (clear * - g n E b a c d e f;grind) | (clear * - g n x b a c d e f;grind) | (clear * - u q p c66 b a c d e f;grind) | (clear * - u q p b a c d e f;grind) | (clear * - o k K u b a c d e f;grind) | (clear * - g k c66 b a c d e f;grind) | (clear * - g x E b a c d e f;grind) | (clear * - u q p m b a c d e f;grind) | (clear * - g o k b a c d e f;grind) | (by_cases G:zb=0<;>by_cases H:l=0<;>first | (clear * - r s c66 m b a c d e f G H;simp only[A0,B7,A7,B4,B5]at r s c66 m<;>grind) | (clear * - k b a c d e f G H;grind) | (clear * - n o k b a c d e f G H;grind) | (clear * - y z A B J C D g n b a c d e f G H;grind))
 .clear * - k t p i j;grind
 .clear * - g o t i j;grind
def ajM {F q r n p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 N L M:ℂ} (h:Iw (zv 1 F q) (yv 1 r n) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨0,0,1,N⟩) (⟨0,1,L,M⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨l,m,p⟩ | ⟨l,m,p⟩ | ⟨l,m,p⟩ | ⟨l,m,p⟩ | ⟨l,m⟩ | ⟨l,m⟩ | ⟨l,m⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,S,T,U,V,W,X,Y,-,x,y,z,A,O,P,Q,c28,i,o,G⟩,⟨s,B,Z,t,H,J,ae,ag,ai,aj,al,am,-,-,-,-,u,ao,C,D,ap,as,au,K,av,aw,ax,ay,-⟩,⟨j,k,a,b⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .by_cases w:(11*r+11*n+16)=0
  .have d:11*r+11*n+16=0:=by clear * - l m p w;grind
   have c:176*r+176*n+121*F+121*q+377=0:=by clear * - l m p w;grind
   by_cases e:N=0<;>by_cases f:L=0<;>by_cases g:M=0<;>first | (clear * - j k a b d c e f g;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - c28 i d c e f g;grind) | (clear * - c28 i o d c e f g;grind) | (clear * - c28 o a d c e f g;grind) | (clear * - c28 a b d c e f g;grind) | (by_cases v:q=0<;>by_cases f1:n=0<;>first | (clear * - j k a b d c e f g v f1;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - x y z A O P Q c28 i o d c e f g v f1;grind)) | (by_cases v:q=0<;>by_cases f1:n=0<;>first | (clear * - j k a b d c e f g v f1;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - x y z A c28 i o H J K b d c e f g v f1;grind)) | (by_cases v:q=0<;>by_cases f1:n=0<;>first | (clear * - j k a b d c e f g v f1;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - x y z A c28 i o H J K a d c e f g v f1;grind))
  .have d:297*r+297*n+377=0:=by clear * - l m p w;grind
   have c: -n+ q=0:=by clear * - l m p w;grind
   have E:176*r+176*n+121*F+121*q+377=0:=by clear * - l m p w;grind
   have R:q=n:=by linear_combination c
   subst R;by_cases e:N=0<;>by_cases f:L=0<;>by_cases g:M=0<;>first | (clear * - j k a b d c E e f g;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - c28 i d c E e f g;grind) | (clear * - i o d c E e f g;grind) | (clear * - u a d c E e f g;grind) | (clear * - u b d c E e f g;grind) | (clear * - a b d c E e f g;grind)
 .clear * - C D l m p;grind
 .clear * - c28 i s B t p;grind
 .clear * - c28 i s B t p;grind
 .clear * - c28 i o G l m;grind
 .have d: -121*r*n+297*r*F+121*r+176*n*F+256*F=0:=by clear * - l m ;grind
  have c:n+ q=0:=by clear * - l m ;grind
  have R: -q=n:=by linear_combination -c
  subst R;by_cases e:N=0<;>by_cases f:L=0<;>by_cases g:M=0<;>first | (clear * - j k a b d c e f g;simp only[A0,B7,A7,B4,B5]at j k a b<;>grind) | (clear * - u C D a d c e f g;grind) | (clear * - c28 i o d c e f g;grind) | (clear * - s B t d c e f g;grind) | (clear * - u C b d c e f g;grind) | (clear * - D a b d c e f g;grind) | (clear * - c28 i G a d c e f g;grind) | (clear * - c0 c3 S T U V W X Y x y z A O P Q c28 i o G s B Z t H J ae ag ai aj al am u ao C D ap as au K av aw ax ay j k a b d c e f g;grind)
 .clear * - c28 s t l m;grind
def ajN {C D A B x p2 p3 r0 y z s t m3 u v w q o:ℂ} (h:Iw (zv 1 C D) (yv 1 A B) (⟨x,0,p2,p3⟩) (⟨r0,0,y,z⟩) (⟨s,0,t,m3⟩) (⟨u,0,v,w⟩) (⟨0,0,1,q⟩) (⟨0,0,1,o⟩)):False:=by
 by_cases r:q=o
 .subst o;obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,d,g,-,m⟩,⟨c32,i,-,j,-,-,-,-,-,-,-,-,-,-,-,-,e,k,-,l,-⟩,⟨-,-,c,f⟩⟩:=h;simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
  first | (clear * - d c32 i j c f ;grind)
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (λ⟨E,F,G,H,J,p⟩=> r (by dsimp only at p;linear_combination p)) with⟨a,b,n⟩ | ⟨a,b,n⟩ | ⟨a,b,n⟩ | ⟨a,b,n⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩<;>
 obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,d,g,-,m⟩,⟨c32,i,-,j,-,-,-,-,-,-,-,-,-,-,-,-,e,k,-,l,-⟩,⟨-,-,c,f⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - d g c32 c f a b;grind
 .clear * - e k c a b;grind
 .clear * - e k l a b;grind
 .clear * - d j c a b;grind
 .clear * - d i c a b;grind
 .clear * - d g m c f a b;grind
 .clear * - e l c a b;grind
def ajO {P Q H p0 p2 p3 r0 r1 r3 m0 m2 m3 n0 n1 n3 t1 N O g1 K L:ℂ} (h:Iw (zv 1 P Q) (yv 0 1 H) (⟨p0,0,p2,p3⟩) (⟨r0,r1,0,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,n1,0,n3⟩) (⟨1,t1,N,O⟩) (⟨1,g1,K,L⟩)):False:=by
 by_cases he:t1=g1/\N=K/\O=L
 .obtain⟨x,y,e2⟩:=he;subst g1 K L;obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,R,S,z,T,U,V,A,-,B,C,W,r,D,s,E,i,X,Y,t⟩,⟨k,F,n,o,Z,ae,ag,ai,aj,al,am,ao,-,-,-,-,l,m,u,d,ap,v,as,G,au,av,aw,ax,-⟩,⟨e,w,f,j⟩⟩:=h;simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
  by_cases a:t1=0<;>by_cases b:N=0<;>by_cases c:O=0<;>first | (clear * - d a b c;grind) | (clear * - i t e f a b c;grind) | (clear * - l u d a b c;grind) | (clear * - l m d a b c;grind) | (clear * - l m u e f a b c;grind) | (by_cases p:(1+P+Q)=0<;>by_cases q:(1+H)=0<;>first | (clear * - e w f j a b c p q;simp only[A0,B7,A7,B4,B5]at e w f j<;>grind) | (clear * - d a b c p q;grind) | (clear * - e a b c p q;grind) | (clear * - f j a b c p q;grind) | (clear * - i t a b c p q;grind) | (clear * - i k F n o a b c p q;grind) | (clear * - z A C r s m d a b c p q;grind) | (clear * - r D s E d v f j a b c p q;grind))
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (λ⟨k0,k1,k2,k3,k4,k5⟩=> he ⟨by dsimp only at k0;linear_combination k0,by dsimp only at k1;linear_combination k1,by dsimp only at k2;linear_combination k2⟩) with⟨g,b1,J⟩ | ⟨g,b1,J⟩ | ⟨g,b1,J⟩ | ⟨g,b1,J⟩ | ⟨g,b1⟩ | ⟨g,b1⟩ | ⟨g,b1⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,R,S,z,T,U,V,A,-,B,C,W,r,D,s,E,i,X,Y,t⟩,⟨k,F,n,o,Z,ae,ag,ai,aj,al,am,ao,-,-,-,-,l,m,u,d,ap,v,as,G,au,av,aw,ax,-⟩,⟨e,w,f,j⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - d g J;grind
 .norm_num at b1
 .norm_num at b1
 .clear * - i k n o e g;grind
 .have x:H+1=0:=by clear * - g b1 ;grind
  have y:H*P+ Q=0:=by clear * - g b1 ;grind
  have s0: -1=H:=by linear_combination -x
  subst s0
  have s1:Q=P:=by linear_combination y
  subst s1;by_cases a:N=0<;>by_cases b:O=0<;>by_cases c:K=0<;>by_cases M:L=0<;>first | (clear * - l x y a b c M;grind) | (clear * - k x y a b c M;grind) | (clear * - B m d v G j x y a b c M;grind) | (clear * - c0 c3 R S z T U V A B C W r D s E i X Y t k F n o Z ae ag ai aj al am ao l m u d ap v as G au av aw ax e w f j x y a b c M;grind)
 .clear * - i k n o e g;grind
 .norm_num at b1
def ajP {y i e G p2 p3 r0 H J B C m3 D E F M N O z A:ℂ} (h:Iw (zv 1 y i) (yv 0 1 e) (⟨G,0,p2,p3⟩) (⟨r0,H,0,J⟩) (⟨B,0,C,m3⟩) (⟨D,E,0,F⟩) (⟨1,M,N,O⟩) (⟨0,1,z,A⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a⟩ | ⟨b,a⟩ | ⟨b,a⟩<;>
 obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,j,-,-,-,-,-,-,-,k,-,l,m,-,-,-,f,-,n,-⟩,⟨-,-,-,g,-,o,p,q,-,-,-,-,-,-,-,-,-,-,c50,d,-,-,r,s,-,-,t,u,-⟩,⟨-,-,v,-⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - g b a;grind
 .norm_num at a
 .norm_num at a
 .have w:e=0:=by clear * - b a c ;grind
  have x:e*y+ i=0:=by clear * - b a c ;grind
  have K:0=e:=by linear_combination -w
  subst K
  have L:0=i:=by linear_combination -x
  subst L;clear * - k l m f n o p q c50 d r s v w x;grind
 .clear * - g d b;grind
 .clear * - j f c50 d t u b a;grind
 .norm_num at a
def ajQ {y w x p0 p1 p3 r0 r2 r3 m0 m1 m3 n0 n2 n3 W X Y T U V:ℂ} (h:Iw (zv 0 1 y) (yv 1 w x) (⟨p0,p1,0,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,m1,0,m3⟩) (⟨n0,0,n2,n3⟩) (⟨1,W,X,Y⟩) (⟨1,T,U,V⟩)):False:=by
 by_cases he:W=T/\X=U/\Y=V
 .obtain⟨R,S,e2⟩:=he;subst T U V;obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,z,o,A,p,-,B,-,-,l,C,D,E,F,G,H,m,-,-,J⟩,⟨q,K,r,n,-,-,-,-,L,M,-,N,-,-,-,-,e,f,c50,d,O,s,-,-,P,Q,-⟩,⟨a,t,g,u⟩⟩:=h;simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
  by_cases i:W=0<;>by_cases j:X=0<;>by_cases k:Y=0<;>first | (clear * - d i j k;grind) | (clear * - m J a g i j k;grind) | (clear * - e c50 d i j k;grind) | (clear * - e f d i j k;grind) | (clear * - e f c50 a g i j k;grind) | (clear * - l e f c50 O s a g i j k;grind) | (by_cases Z:(1+y)=0<;>by_cases f1:(16+11*w+11*x)=0<;>first | (clear * - a t g u i j k Z f1;simp only[A0,B7,A7,B4,B5]at a t g u<;>grind) | (clear * - o p B l C D E F G H f c50 d i j k Z f1;grind))
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (λ⟨k0,k1,k2,k3,k4,k5⟩=> he ⟨by dsimp only at k0;linear_combination k0,by dsimp only at k1;linear_combination k1,by dsimp only at k2;linear_combination k2⟩) with⟨b,c,v⟩ | ⟨b,c,v⟩ | ⟨b,c,v⟩ | ⟨b,c,v⟩ | ⟨b,c⟩ | ⟨b,c⟩ | ⟨b,c⟩<;>
 obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,z,o,A,p,-,B,-,-,l,C,D,E,F,G,H,m,-,-,J⟩,⟨q,K,r,n,-,-,-,-,L,M,-,N,-,-,-,-,e,f,c50,d,O,s,-,-,P,Q,-⟩,⟨a,t,g,u⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - d b v;grind
 .norm_num at c
 .norm_num at c
 .clear * - m q r n a b;grind
 .have R:w- x=0:=by clear * - b c ;grind
  have S:y+1=0:=by clear * - b c ;grind
  have s0:x=w:=by linear_combination -R
  subst s0
  have s1: -1=y:=by linear_combination -S
  subst s1;clear * - z o A p l K n L M N e f d s P Q R S;grind
 .clear * - m q r n a b;grind
 .norm_num at c
def ajR {f s yb A B p3 r0 C D v w m3 x y z F G H t u:ℂ} (h:Iw (zv 0 1 f) (yv 1 s yb) (⟨A,B,0,p3⟩) (⟨r0,0,C,D⟩) (⟨v,w,0,m3⟩) (⟨x,0,y,z⟩) (⟨1,F,G,H⟩) (⟨0,1,t,u⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a⟩ | ⟨b,a⟩ | ⟨b,a⟩<;>
 obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,i,-,-,-,-,-,-,j,-⟩,⟨-,-,-,k,-,-,-,-,-,-,-,-,-,-,-,-,l,m,n,d,o,-,p,q,-⟩,-⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - k b a;grind
 .norm_num at a
 .norm_num at a
 .have g:yb=0:=by clear * - b a c ;grind
  have e:f=0:=by clear * - b a c ;grind
  have r:0=yb:=by linear_combination -g
  subst r
  have E:0=f:=by linear_combination -e
  subst E;clear * - i j l m n d o p q g e;grind
 .clear * - k d b;grind
 .have g:297*s+176*yb+256=0:=by clear * - b a ;grind
  have e:f=0:=by clear * - b a ;grind
  have r:0=f:=by linear_combination -e
  subst r;clear * - i j l m n d o p q g e;grind
 .norm_num at a
def ajS {g z i J K p3 r0 L M D E m3 F G H O P A B C:ℂ} (h:Iw (zv 0 1 g) (yv 1 z i) (⟨J,K,0,p3⟩) (⟨r0,0,L,M⟩) (⟨D,E,0,m3⟩) (⟨F,0,G,H⟩) (⟨0,1,O,P⟩) (⟨1,A,B,C⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a,c⟩ | ⟨b,a⟩ | ⟨b,a⟩ | ⟨b,a⟩<;>
 obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,m,n,-,o,p,j,-⟩,⟨q,r,k,d,s,-,t,u,-,-,-,-,-,-,-,-,-,-,v,e,-,-,w,x,-⟩,⟨-,-,y,-⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - e b a;grind
 .norm_num at a
 .norm_num at a
 .have e0:i=0:=by clear * - b a c ;grind
  have f:g=0:=by clear * - b a c ;grind
  have l:0=i:=by linear_combination -e0
  subst l
  have N:0=g:=by linear_combination -f
  subst N;clear * - n o p j k d v e w x y e0 f;grind
 .clear * - d e b;grind
 .have e0:297*z+176*i+256=0:=by clear * - b a ;grind
  have f:g=0:=by clear * - b a ;grind
  have l:0=g:=by linear_combination -f
  subst l;clear * - m j q r k d s t u e0 f;grind
 .norm_num at a
def ajT {G F Y Z p3 r0 r1 r3 T U m3 V W X D E P B C O:ℂ} (h:Iw (zv 0 1 G) (yv 0 1 F) (⟨Y,Z,0,p3⟩) (⟨r0,r1,0,r3⟩) (⟨T,U,0,m3⟩) (⟨V,W,0,X⟩) (⟨1,D,E,P⟩) (⟨1,B,C,O⟩)):False:=by
 by_cases e:D=B/\E=C/\P=O
 .obtain⟨N,e1,e2⟩:=e;subst B C O;obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,H,J,u,v,-,w,-,-,p,-,-,-,-,-,-,j,c29,l,-⟩,⟨-,K,L,M,-,-,-,-,-,-,-,-,-,-,-,-,-,f,x,q,-,r,-,-,-,y,-,s,-⟩,⟨a,z,m,A⟩⟩:=h;simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
  by_cases b:D=0<;>by_cases c:E=0<;>by_cases d:P=0<;>first | (clear * - m b c d;grind) | (clear * - j c29 a b c d;grind) | (clear * - f x q b c d;grind) | (clear * - u v w p r y s a b c d;grind)
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (λ⟨Q,R,S,k3,k4,k5⟩=> e ⟨by dsimp only at Q;linear_combination Q,by dsimp only at R;linear_combination R,by dsimp only at S;linear_combination S⟩) with⟨g,k,t⟩ | ⟨g,k,t⟩ | ⟨g,k,t⟩ | ⟨g,k,t⟩ | ⟨g,k⟩ | ⟨g,k⟩ | ⟨g,k⟩<;>
 obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,H,J,u,v,-,w,-,-,p,-,-,-,-,-,-,j,c29,l,-⟩,⟨-,K,L,M,-,-,-,-,-,-,-,-,-,-,-,-,-,f,x,q,-,r,-,-,-,y,-,s,-⟩,⟨a,z,m,A⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - f a k;grind
 .by_cases b:D=0<;>by_cases c:B=0<;>by_cases d:E=0<;>by_cases i:C=0<;>first | (clear * - m e b c d i;grind) | (clear * - f x q e b c d i;grind) | (clear * - K L M e b c d i;grind) | (clear * - j c29 l e b c d i;grind) | (by_cases n:(1+G)=0<;>by_cases o:(1+F)=0<;>first | (clear * - a z m A e b c d i n o;simp only[A0,B7,A7,B4,B5]at a z m A<;>grind) | (clear * - f e b c d i n o;grind) | (clear * - a e b c d i n o;grind) | (clear * - c29 l e b c d i n o;grind) | (clear * - j c29 l e b c d i n o;grind) | (clear * - p j c29 r e b c d i n o;grind) | (clear * - u v w j c29 l y s e b c d i n o;grind))
 .clear * - a g t;grind
 .clear * - a g t;grind
 .have N:F+ G=0:=by clear * - g k ;grind
  have s0: -G=F:=by linear_combination -N
  subst s0;clear * - H J p f q r s a N;grind
 .clear * - f a g;grind
 .clear * - f a g;grind
set_option maxHeartbeats 0 in
def ajH {x zb u n p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 t1 W X T U:ℂ} (h:Iw (zv 1 x zb) (yv 1 u n) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨1,t1,W,X⟩) (⟨0,1,T,U⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨l,m,v⟩ | ⟨l,m,v⟩ | ⟨l,m,v⟩ | ⟨l,m,v⟩ | ⟨l,m⟩ | ⟨l,m⟩ | ⟨l,m⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,E,F,G,H,J,Z,ae,-,K,L,M,N,O,ag,ai,o,r,z,C⟩,⟨aj,s,j,k,al,am,P,Q,ao,ap,R,S,-,-,-,-,i,as,c50,g,au,av,aw,ax,ay,az,aA,aB,-⟩,⟨D,p,q,t⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - j k l m v;grind
 .clear * - c50 g l m v;grind
 .by_cases w:u=0
  .have b:u=0:=by clear * - l m v w;grind
   have a:u+ x=0:=by clear * - l m v w;grind
   have y:0=u:=by linear_combination -b
   subst y
   have V:0=x:=by linear_combination -a
   subst V;by_cases c:W=0<;>by_cases d:T=0<;>by_cases e:X=0<;>by_cases f:U=0
   ·(clear * - o r z b a c d e f;grind)
   rotate_left;rotate_left;rotate_left
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   all_goals (by_cases A:n=0<;>by_cases B:zb=0<;>first | (clear * - c0 c3 E F G H J Z ae K L M N O ag ai o r z C aj s j k al am P Q ao ap R S i as c50 g au av aw ax ay az aA aB D p q t b a c d e f A B;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at D p q t<;>grind))
  .have b:297*u+55*n+135=0:=by clear * - l m v w;grind
   have a: -n+ zb=0:=by clear * - l m v w;grind
   have Y:u+ x=0:=by clear * - l m v w;grind
   have y: -5*n/27-5/11=u:=by linear_combination (-1:ℂ)*(1/297:ℂ)*b
   subst y
   have V:zb=n:=by linear_combination a
   subst V
   have s2:5*zb/27+5/11=x:=by linear_combination -Y
   subst s2;first | (clear * - o j c50 p t b a Y;grind)
 .by_cases w:n=0
  .have b:n=0:=by clear * - l m v w;grind
   have a:n+ zb=0:=by clear * - l m v w;grind
   have y:0=n:=by linear_combination -b
   subst y
   have V:0=zb:=by linear_combination -a
   subst V;by_cases c:X=0<;>by_cases d:U=0<;>by_cases e:W=0<;>by_cases f:T=0
   ·(clear * - o r z b a c d e f;grind)
   rotate_left;rotate_left;rotate_left
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - s j k b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   ·(clear * - i c50 g b a c d e f;grind)
   all_goals (by_cases A:u=0<;>by_cases B:x=0<;>first | (clear * - c0 c3 E F G H J Z ae K L M N O ag ai o r z C aj s j k al am P Q ao ap R S i as c50 g au av aw ax ay az aA aB D p q t b a c d e f A B;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at D p q t<;>grind))
  .have b:55*u+297*n+135=0:=by clear * - l m v w;grind
   have a:n+ zb=0:=by clear * - l m v w;grind
   have Y:297*n+55*x+135=0:=by clear * - l m v w;grind
   have y: -zb=n:=by linear_combination -a
   subst y;first | (clear * - o k g p q b a Y;grind)
 .clear * - o r j k l m;grind
 .have b: -121*u*n+297*u*x+121*u+176*n*x+256*x=0:=by clear * - l m ;grind
  have a:n+ zb=0:=by clear * - l m ;grind
  have y: -zb=n:=by linear_combination -a
  subst y;by_cases c:W=0<;>by_cases d:X=0<;>by_cases e:T=0<;>by_cases f:U=0
  ·(clear * - o r z C b a c d e f;grind)
  rotate_left
  ·(clear * - k c50 g b a c d e f;grind)
  ·(clear * - k c50 g b a c d e f;grind)
  ·(clear * - r j k b a c d e f;grind)
  ·(clear * - i c50 t b a c d e f;grind)
  ·(clear * - o j k p b a c d e f;grind)
  ·(clear * - i g t b a c d e f;grind)
  rotate_left;rotate_left
  ·(clear * - i c50 g q b a c d e f;grind)
  ·(clear * - k c50 g b a c d e f;grind)
  ·(clear * - o r s j k b a c d e f;grind)
  ·(clear * - i c50 t b a c d e f;grind)
  ·(clear * - i c50 g q b a c d e f;grind)
  ·(clear * - g q t b a c d e f;grind)
  all_goals (by_cases A:x=0<;>by_cases B:u=0<;>first | (clear * - K L M N O o r j k P Q c50 p q b a c d e f A B;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at p q<;>grind))
 .have b: -121*u*n+176*u*zb+297*n*zb+121*n+256*zb=0:=by clear * - l m ;grind
  have a:u+ x=0:=by clear * - l m ;grind
  have y: -x=u:=by linear_combination -a
  subst y;by_cases c:W=0<;>by_cases d:X=0<;>by_cases e:T=0<;>by_cases f:U=0
  ·(clear * - o r z C b a c d e f;grind)
  ·(clear * - j c50 g b a c d e f;grind)
  rotate_left
  ·(clear * - j c50 g b a c d e f;grind)
  rotate_left
  ·(clear * - i c50 g t b a c d e f;grind)
  rotate_left
  ·(clear * - j c50 g b a c d e f;grind)
  ·(clear * - r j k b a c d e f;grind)
  ·(clear * - o j k p b a c d e f;grind)
  ·(clear * - i g q b a c d e f;grind)
  ·(clear * - i g q b a c d e f;grind)
  ·(clear * - s j k p b a c d e f;grind)
  ·(clear * - i c50 g t b a c d e f;grind)
  ·(clear * - i g q b a c d e f;grind)
  ·(clear * - g q t b a c d e f;grind)
  all_goals (by_cases A:x=0<;>by_cases B:n=0<;>by_cases f2:zb=0<;>first | (clear * - r j g p b a c d e f A B f2;grind (ringSteps:=20000)) | (clear * - E F G H J o r j k R S c50 g p b a c d e f A B f2;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at p<;>grind))
def ajI {A s x l p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 K t2 L J:ℂ} (h:Iw (zv 1 A s) (yv 1 x l) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨1,K,t2,L⟩) (⟨0,0,1,J⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨b0,i,r⟩ | ⟨b0,i,r⟩ | ⟨b0,i,r⟩ | ⟨b0,i,r⟩ | ⟨b0,i⟩ | ⟨b0,i⟩ | ⟨b0,i⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,M,N,O,P,Q,R,S,-,B,C,D,E,F,G,H,f,j,u,v⟩,⟨c32,g,q,m,T,U,V,W,X,Y,Z,ae,-,-,-,-,n,o,ag,p,ai,aj,al,am,ao,ap,as,au,-⟩,⟨av,aw,t,y⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - q m b0 i r;grind
 .clear * - f j g t y b0 i r;grind
 .clear * - n o p b0 i;grind
 .by_cases w:l=0
  .have b:l=0:=by clear * - b0 i r w;grind
   have a:l+ s=0:=by clear * - b0 i r w;grind
   have z:0=l:=by linear_combination -b
   subst z
   have s1:0=s:=by linear_combination -a
   subst s1;by_cases c:K=0<;>by_cases d:L=0<;>by_cases e:J=0
   ·(clear * - f j u b a c d e;grind)
   ·(clear * - n o p b a c d e;grind)
   ·(clear * - g q m b a c d e;grind)
   ·(clear * - n o p b a c d e;grind)
   rotate_left
   ·(clear * - n o p b a c d e;grind)
   ·(clear * - g q m b a c d e;grind)
   ·(clear * - n o p b a c d e;grind)
   all_goals (first | (clear * - c0 c3 M N O P Q R S B C D E F G H f j u v c32 g q m T U V W X Y Z ae n o ag p ai aj al am ao ap as au av aw t y b a c d e;grind))
  .have b:55*x+297*l+135=0:=by clear * - b0 i r w;grind
   have a:l+ s=0:=by clear * - b0 i r w;grind
   have e2:297*l+55*A+135=0:=by clear * - b0 i r w;grind
   have z: -s=l:=by linear_combination -a
   subst z;first | (clear * - m p b a e2;grind)
 .have b: -176*x*l+121*x*s-176*l^2-121*l*s-377*l=0:=by clear * - b0 i ;grind
  have a:176*x+176*l+121*A+121*s+377=0:=by clear * - b0 i ;grind
  have z: -l-11*A/16-11*s/16-377/176=x:=by linear_combination (-1:ℂ)*(1/176:ℂ)*a
  subst z;by_cases c:K=0<;>by_cases d:t2=0<;>by_cases e:L=0<;>by_cases k:J=0
  ·(clear * - f u v b a c d e k;grind)
  ·(clear * - f j v b a c d e k;grind)
  ·(clear * - f j u b a c d e k;grind)
  ·(clear * - f j v b a c d e k;grind)
  ·(clear * - f j u b a c d e k;grind)
  ·(clear * - f j v b a c d e k;grind)
  ·(clear * - g q m b a c d e k;grind)
  ·(clear * - g q m b a c d e k;grind)
  rotate_left
  ·(clear * - f n o b a c d e k;grind)
  ·(clear * - c32 g n o b a c d e k;grind)
  ·(clear * - j g y b a c d e k;grind)
  ·(clear * - f g t b a c d e k;grind)
  ·(clear * - j g t b a c d e k;grind)
  ·(clear * - j c32 g b a c d e k;grind)
  ·(clear * - f c32 g b a c d e k;grind)
  all_goals (by_cases f0:A=0<;>by_cases f1:l=0<;>by_cases f2:s=0<;>first | (clear * - q m b a c d e k f0 f1 f2;grind (ringSteps:=20000)) | (clear * - B C D E F G H f g m n o t b a c d e k f0 f1 f2;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at t<;>grind))
 .clear * - m o p b0 i;grind
 .clear * - f n p b0 i;grind
set_option maxHeartbeats 0 in
def ajJ {za u r p p0 p2 p3 r0 r2 r3 m0 m2 m3 n0 n2 n3 X Y g1 U V:ℂ} (h:Iw (zv 1 za u) (yv 1 r p) (⟨p0,0,p2,p3⟩) (⟨r0,0,r2,r3⟩) (⟨m0,0,m2,m3⟩) (⟨n0,0,n2,n3⟩) (⟨0,1,X,Y⟩) (⟨1,g1,U,V⟩)):False:=by
 rcases Rc _ _ _ _ _ _ _ _ h.2.1 (by norm_num) with⟨n,o,t⟩ | ⟨n,o,t⟩ | ⟨n,o,t⟩ | ⟨n,o,t⟩ | ⟨n,o⟩ | ⟨n,o⟩ | ⟨n,o⟩<;>
 obtain⟨⟨c0,-,-,c3,-,-,-,-,-,-,-,-,-,D,E,F,G,ae,ag,ai,-,H,aj,J,K,al,L,M,m,s,B,am⟩,⟨q,ao,j,k,ap,as,au,av,aw,ax,N,O,-,-,-,-,ay,l,g,c51,az,aA,P,Q,aB,aC,R,S,-⟩,⟨C,i,x,v⟩⟩:=h<;>
 simp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
 .clear * - g c51 n o t;grind
 .clear * - j k n o t;grind
 .by_cases w:r=0
  .have b:r=0:=by clear * - n o t w;grind
   have a:r+ za=0:=by clear * - n o t w;grind
   have y:0=r:=by linear_combination -b
   subst y
   have W:0=za:=by linear_combination -a
   subst W;by_cases c:X=0<;>by_cases d:U=0<;>by_cases e:Y=0<;>by_cases f:V=0
   ·(clear * - m s B b a c d e f;grind)
   rotate_left;rotate_left;rotate_left
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   all_goals (by_cases z:p=0<;>by_cases A:u=0<;>first | (clear * - c0 c3 D E F G ae ag ai H aj J K al L M m s B am q ao j k ap as au av aw ax N O ay l g c51 az aA P Q aB aC R S C i x v b a c d e f z A;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at C i x v<;>grind))
  .have b:297*r+55*p+135=0:=by clear * - n o t w;grind
   have a: -p+ u=0:=by clear * - n o t w;grind
   have Z:r+ za=0:=by clear * - n o t w;grind
   have y: -5*p/27-5/11=r:=by linear_combination (-1:ℂ)*(1/297:ℂ)*b
   subst y
   have W:u=p:=by linear_combination a
   subst W
   have s2:5*u/27+5/11=za:=by linear_combination -Z
   subst s2;first | (clear * - m j g i v b a Z;grind)
 .by_cases w:p=0
  .have b:p=0:=by clear * - n o t w;grind
   have a:p+ u=0:=by clear * - n o t w;grind
   have y:0=p:=by linear_combination -b
   subst y
   have W:0=u:=by linear_combination -a
   subst W;by_cases c:Y=0<;>by_cases d:V=0<;>by_cases e:X=0<;>by_cases f:U=0
   ·(clear * - m s B b a c d e f;grind)
   rotate_left;rotate_left;rotate_left
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - q j k b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   ·(clear * - l g c51 b a c d e f;grind)
   all_goals (by_cases z:r=0<;>by_cases A:za=0<;>first | (clear * - c0 c3 D E F G ae ag ai H aj J K al L M m s B am q ao j k ap as au av aw ax N O ay l g c51 az aA P Q aB aC R S C i x v b a c d e f z A;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at C i x v<;>grind (ringSteps:=50000)))
  .have b:55*r+297*p+135=0:=by clear * - n o t w;grind
   have a:p+ u=0:=by clear * - n o t w;grind
   have Z:297*p+55*za+135=0:=by clear * - n o t w;grind
   have y: -u=p:=by linear_combination -a
   subst y;first | (clear * - m k c51 i x b a Z;grind)
 .clear * - m j k n o;grind
 .have b: -121*r*p+297*r*za+121*r+176*p*za+256*za=0:=by clear * - n o ;grind
  have a:p+ u=0:=by clear * - n o ;grind
  have y: -u=p:=by linear_combination -a
  subst y;by_cases c:X=0<;>by_cases d:Y=0<;>by_cases e:g1=0<;>by_cases f:V=0;rotate_left
  ·(clear * - j g c51 b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  rotate_left
  ·(clear * - g c51 v b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - m s j k b a c d e f;grind)
  ·(clear * - m q j k b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - m s j k b a c d e f;grind)
  ·(clear * - g c51 v b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  all_goals (by_cases z:U=0<;>by_cases A:za=0<;>by_cases T:r=0<;>first | (clear * - m s q j i b a c d e f z A T;grind (ringSteps:=20000)) | (clear * - D E F G m s q j k N O R S i v b a c d e f z A T;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at i v<;>grind))
 .have b: -121*r*p+176*r*u+297*p*u+121*p+256*u=0:=by clear * - n o ;grind
  have a:r+ za=0:=by clear * - n o ;grind
  have y: -za=r:=by linear_combination -a
  subst y;by_cases c:X=0<;>by_cases d:Y=0<;>by_cases e:g1=0<;>by_cases f:U=0;rotate_left
  ·(clear * - k g c51 b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - m s j k b a c d e f;grind)
  ·(clear * - m q j k b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  rotate_left
  ·(clear * - g c51 x b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - m s j k b a c d e f;grind)
  ·(clear * - g c51 x b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  ·(clear * - i b a c d e f;grind)
  all_goals (by_cases z:V=0<;>by_cases A:za=0<;>by_cases T:p=0<;>by_cases f3:u=0<;>first | (clear * - l g b a c d e f z A T f3;grind (ringSteps:=20000)) | (clear * - H J K L M m s j k g c51 P Q i b a c d e f z A T f3;simp only[A0,B7,A7,D4,B4,B5,D9,C8,E4,E5]at i<;>grind))
set_option maxHeartbeats 0 in
def akF {p q n o f p2 p3 r0 g h i j m3 k l m:ℂ} (t b:V4)
  (a:Iw (zv 1 p q) (yv 1 n o) ⟨f,0,p2,p3⟩ ⟨r0,0,g,h⟩ ⟨i,0,j,m3⟩ ⟨k,0,l,m⟩ t b)
  (e:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (d:(b.x0=1\/b.x0=0/\(b.x1=1\/b.x1=0/\(b.x2=1\/b.x2=0/\b.x3=1)))) (hn:NZ ⟨f,0,p2,p3⟩\/NZ ⟨r0,0,g,h⟩):False:=by
 obtain⟨w,x,tq,y⟩:=t;obtain⟨r,s,u,v⟩:=b;dsimp only at e d;rcases e with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases d with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have c:=a
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at c
 .exact ajG a hn
 .exact ajH a
 .exact ajI a
 .clear c;obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,_,-,_,_,-,-,-,_,-⟩,⟨-,-,_,-,_,-,_,_,-,-,-,-,-,-,-,-,_,_,_,-,-,_,_,-⟩,⟨-,-,-,_⟩⟩:=a;dsimp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *;grind
 .exact ajJ a
 .grind
 .exact ajK a
 .grind
 .exact ajL a
 .exact ajM a
 .exact ajN a
 .grind
 .clear c;obtain⟨⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,_,-,_,_,-,-,-,_,-⟩,⟨-,_,_,-,-,_,_,-,-,-,-,-,-,-,-,-,_,-,_,_,-,-,_,_,-⟩,⟨-,-,-,_⟩⟩:=a;dsimp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *;grind
 all_goals grind
def akG {o p n k p2 p3 r0 l m f g m3 h i j:ℂ} (t a:V4)
  (b:Iw (zv 1 o p) (yv 0 1 n) ⟨k,0,p2,p3⟩ ⟨r0,l,0,m⟩ ⟨f,0,g,m3⟩ ⟨h,i,0,j⟩ t a)
  (d:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (c:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨v,w,tq,x⟩:=t;obtain⟨q,r,s,u⟩:=a;dsimp only at d c;rcases d with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have e:=b
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at e
 .exact ajO b
 .exact ajP b
 all_goals grind
def akH {n o k p2 p3 r0 l m f g m3 h i j:ℂ} (t a:V4)
  (e:Iw (zv 1 n o) (yv 0 0 1) ⟨k,0,p2,p3⟩ ⟨r0,l,m,0⟩ ⟨f,0,g,m3⟩ ⟨h,i,j,0⟩ t a)
  (c:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (b:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨u,v,tq,w⟩:=t;obtain⟨p,q,r,s⟩:=a;dsimp only at c b;rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases b with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have d:=e
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at d
 all_goals grind
def akI {q o p k l p3 r0 m n f g m3 h i j:ℂ} (t a:V4)
  (b:Iw (zv 0 1 q) (yv 1 o p) ⟨k,l,0,p3⟩ ⟨r0,0,m,n⟩ ⟨f,g,0,m3⟩ ⟨h,0,i,j⟩ t a)
  (d:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (c:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨w,x,tq,y⟩:=t;obtain⟨r,s,u,v⟩:=a;dsimp only at d c;rcases d with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have e:=b
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at e
 .exact ajQ b
 .exact ajR b
 .grind
 .grind
 .exact ajS b
 all_goals grind
def akJ {p o k l p3 r0 m n f g m3 h i j:ℂ} (t a:V4)
  (c:Iw (zv 0 1 p) (yv 0 1 o) ⟨k,l,0,p3⟩ ⟨r0,m,0,n⟩ ⟨f,g,0,m3⟩ ⟨h,i,0,j⟩ t a)
  (d:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (b:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨v,w,tq,x⟩:=t;obtain⟨q,r,s,u⟩:=a;dsimp only at d b;rcases d with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases b with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have e:=c
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at e
 .exact ajT c
 all_goals grind
def akK {o k l p3 r0 m n f g m3 h i j:ℂ} (t a:V4)
  (e:Iw (zv 0 1 o) (yv 0 0 1) ⟨k,l,0,p3⟩ ⟨r0,m,n,0⟩ ⟨f,g,0,m3⟩ ⟨h,i,j,0⟩ t a)
  (c:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (b:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨u,v,tq,w⟩:=t;obtain⟨p,q,r,s⟩:=a;dsimp only at c b;rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases b with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have d:=e
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at d
 all_goals grind
def akL {p q l m p2 r0 n o f g h i j k:ℂ} (t a:V4)
  (e:Iw (zv 0 0 1) (yv 1 p q) ⟨l,m,p2,0⟩ ⟨r0,0,n,o⟩ ⟨f,g,h,0⟩ ⟨i,0,j,k⟩ t a)
  (c:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (b:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨w,x,tq,y⟩:=t;obtain⟨r,s,u,v⟩:=a;dsimp only at c b;rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases b with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have d:=e
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at d
 all_goals grind
def akM {p l m p2 r0 n o f g h i j k:ℂ} (t a:V4)
  (e:Iw (zv 0 0 1) (yv 0 1 p) ⟨l,m,p2,0⟩ ⟨r0,n,0,o⟩ ⟨f,g,h,0⟩ ⟨i,j,0,k⟩ t a)
  (c:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (b:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨v,w,tq,x⟩:=t;obtain⟨q,r,s,u⟩:=a;dsimp only at c b;rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases b with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have d:=e
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at d
 all_goals grind
def akN {l m p2 r0 n o f g h i j k:ℂ} (t a:V4)
  (e:Iw (zv 0 0 1) (yv 0 0 1) ⟨l,m,p2,0⟩ ⟨r0,n,o,0⟩ ⟨f,g,h,0⟩ ⟨i,j,k,0⟩ t a)
  (c:(t.x0=1\/t.x0=0/\(t.x1=1\/t.x1=0/\(t.x2=1\/t.x2=0/\t.x3=1))))
  (b:(a.x0=1\/a.x0=0/\(a.x1=1\/a.x1=0/\(a.x2=1\/a.x2=0/\a.x3=1)))):False:=by
 obtain⟨u,v,tq,w⟩:=t;obtain⟨p,q,r,s⟩:=a;dsimp only at c b;rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩<;>
 rcases b with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have d:=e
 all_goals dsimp only[Iw,QF,O2,Rg,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at d
 all_goals grind
def aiO:abX:=by
 intro z y i j g h t d b f e c a hn;obtain⟨u,v,p2,p3⟩:=i;obtain⟨r0,w,x,r3⟩:=j;obtain⟨m,n,o,m3⟩:=g;obtain⟨p,q,r,s⟩:=h;dsimp only at f e;rcases f with⟨⟨l,B,rfl⟩,rfl,rfl⟩ | ⟨⟨l,rfl⟩,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩<;>
 rcases e with⟨⟨k,A,rfl⟩,rfl,rfl⟩ | ⟨⟨k,rfl⟩,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
 .exact akF t d b c a hn
 .exact akG t d b c a
 .exact akH t d b c a
 .exact akI t d b c a
 .exact akJ t d b c a
 .exact akK t d b c a
 .exact akL t d b c a
 .exact akM t d b c a
 .exact akN t d b c a
def akO {h i:ℂ} (x0 x1 a b:V4)
  (g:Mh (zv 1 h i) (yv 0 0 1) x0 x1 a b) (e:x0.x1=0) (d:x1.x3=0)
  (hx:XC x0 x1) (c:AC a):False:=by
 obtain⟨r,s,t,u⟩:=x0;obtain⟨v,w,x,y⟩:=x1;obtain⟨j,k,l,m⟩:=a;obtain⟨n,o,p,q⟩:=b;dsimp only[XC,AC]at e d hx c;subst e d;simp only[G9,C8,B4,B5,H9,I0,I1,I3]at hx;rcases hx with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩⟩⟩<;>
 rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have f:=g
 all_goals dsimp only[Mh,TH,Ri,Yy,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at f
 all_goals grind
def akP {h:ℂ} (x0 x1 a b:V4)
  (g:Mh (zv 0 1 h) (yv 0 0 1) x0 x1 a b) (e:x0.x2=0) (d:x1.x3=0)
  (hx:XC x0 x1) (c:AC a):False:=by
 obtain⟨q,r,s,t⟩:=x0;obtain⟨u,v,w,x⟩:=x1;obtain⟨i,j,k,l⟩:=a;obtain⟨m,n,o,p⟩:=b;dsimp only[XC,AC]at e d hx c;subst e d;simp only[G9,C8,B4,B5,H9,I0,I1,I3]at hx;rcases hx with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩⟩⟩<;>
 rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have f:=g
 all_goals dsimp only[Mh,TH,Ri,Yy,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at f
 all_goals grind
def akQ {z A:ℂ} (x0 x1 a b:V4)
  (r:Mh (zv 0 0 1) (yv 1 z A) x0 x1 a b) (u:x0.x3=0) (t:x1.x1=0)
  (l:XC x0 x1) (s:AC a):False:=by
 obtain⟨m,n,o,p⟩:=x0;obtain⟨X,Y,Z,f3⟩:=x1;obtain⟨Q,R,S,T⟩:=a;obtain⟨v,w,x,y⟩:=b;dsimp only[XC,AC]at u t l s;subst u t;simp only[G9,C8,B4,B5,H9,I0,I1,I3]at l;rcases l with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩⟩⟩<;>
 rcases s with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have q:=r
 all_goals dsimp only[Mh,TH,Ri,Yy,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at q
 .clear q;obtain⟨⟨U,V,h,i,j,k,c6,c7,-,W,B,c11,c,d,-,C,D,e,f,g,E,F,G⟩,⟨H,J,K,L,M,N,O,P⟩,-⟩:=r;dsimp only[mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at *
  have m:v=0:=by clear h i j k c6 c7 c11 c d e f g;grind
  have n:w=0:=by clear h i j k c6 c7 c11 c d e f g;grind
  have o:x=0:=by clear h i j k c6 c7 c11 c d e f g;grind
  have p:y=0:=by clear h i j k c6 c7 c11 c d e f g;grind
  subst m n o p;grind
 all_goals grind
def akR {h:ℂ} (x0 x1 a b:V4)
  (g:Mh (zv 0 0 1) (yv 0 1 h) x0 x1 a b) (e:x0.x3=0) (d:x1.x2=0)
  (hx:XC x0 x1) (c:AC a):False:=by
 obtain⟨q,r,s,t⟩:=x0;obtain⟨u,v,w,x⟩:=x1;obtain⟨i,j,k,l⟩:=a;obtain⟨m,n,o,p⟩:=b;dsimp only[XC,AC]at e d hx c;subst e d;simp only[G9,C8,B4,B5,H9,I0,I1,I3]at hx;rcases hx with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩⟩⟩<;>
 rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have f:=g
 all_goals dsimp only[Mh,TH,Ri,Yy,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at f
 all_goals grind
def akS (x0 x1 a b:V4)
  (g:Mh (zv 0 0 1) (yv 0 0 1) x0 x1 a b) (e:x0.x3=0) (d:x1.x3=0)
  (hx:XC x0 x1) (c:AC a):False:=by
 obtain⟨p,q,r,s⟩:=x0;obtain⟨t,u,v,w⟩:=x1;obtain⟨h,i,j,k⟩:=a;obtain⟨l,m,n,o⟩:=b;dsimp only[XC,AC]at e d hx c;subst e d;simp only[G9,C8,B4,B5,H9,I0,I1,I3]at hx;rcases hx with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩⟩⟩<;>
 rcases c with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩;all_goals have f:=g
 all_goals dsimp only[Mh,TH,Ri,Yy,mp,me,lu,mh,mj,zv,yv,B0,B1,B2,B3]at f
 all_goals grind
def fi (u:V4):V4:=⟨5*u.x1+3*u.x2+3*u.x3,5*u.x0+3*u.x2+3*u.x3,3*u.x0+3*u.x1+2*u.x3,
 3*u.x0+3*u.x1+2*u.x2⟩
def fe (a b u:V4):V4:=
  ⟨(2*b.x3+ b.x2+2*a.x2+ a.x3)*u.x1+(b.x3+ b.x1+2*a.x1+ a.x3)*u.x2+(b.x2+2*b.x1+ a.x1+ a.x2)*u.x3,
   (2*b.x3+ b.x2+2*a.x2+ a.x3)*u.x0+(b.x3+ b.x0+2*a.x0+ a.x3)*u.x2+(b.x2+2*b.x0+ a.x0+ a.x2)*u.x3,
   (b.x3+ b.x1+2*a.x1+ a.x3)*u.x0+(b.x3+ b.x0+2*a.x0+ a.x3)*u.x1+(b.x1+ b.x0+ a.x0+ a.x1)*u.x3,
   (b.x2+2*b.x1+ a.x1+ a.x2)*u.x0+(b.x2+2*b.x0+ a.x0+ a.x2)*u.x1+(b.x1+ b.x0+ a.x0+ a.x1)*u.x2⟩
def Ma (a b c d e f:ℂ): Prop :=b*f- c*e=0/\c*d- a*f=0/\a*e- b*d=0
def WY (g h u3 d e f a b c:ℂ): Prop :=
 (a*d+ b*e+ c*f)*g=(a*g+ b*h+ c*u3)*d/\
 (a*d+ b*e+ c*f)*h=(a*g+ b*h+ c*u3)*e/\
 (a*d+ b*e+ c*f)*u3=(a*g+ b*h+ c*u3)*f
def TI (a b c d e f m n u3 j k l g h i:ℂ): Prop :=Ma a b c d e f\/WY m n u3 j k l g h i
def Xq (e f g h i j d m u3 n k l a b c:ℂ) (o:e*d+ f*m+ g*u3=0)
  (p:h*d+ i*m+ j*u3=0) (q:e*n+ f*k+ g*l=0) (r:h*n+ i*k+ j*l=0)  :
  TI e f g h i j d m u3 n k l a b c:=by
 unfold TI Ma WY;by_cases s:f*j- g*i=0
 .by_cases t:g*h- e*j=0
  .by_cases u:e*i- f*h=0
   .exact Or.inl ⟨s,t,u⟩
   .right;refine⟨?_,?_,?_⟩
    .exact mul_left_cancel₀ u (by linear_combination (-j*l*b+i*l*c)*o+(g*l*b-f*l*c)*p+(-h*d*b-i*m*b-i*u3*c)*q+(e*d*b+f*m*b+f*u3*c)*r)
    .exact mul_left_cancel₀ u (by linear_combination (j*l*a-h*l*c)*o+(-g*l*a+e*l*c)*p+(h*d*a+i*m*a+h*u3*c)*q+(-e*d*a-f*m*a-e*u3*c)*r)
    .exact mul_left_cancel₀ u (by linear_combination (-i*l*a+h*l*b)*o+(f*l*a-e*l*b)*p+(i*u3*a-h*u3*b)*q+(-f*u3*a+e*u3*b)*r)
  .right;refine⟨?_,?_,?_⟩
   .exact mul_left_cancel₀ t (by linear_combination (-j*k*b+i*k*c)*o+(g*k*b-f*k*c)*p+(j*m*b+h*d*c+j*u3*c)*q+(-g*m*b-e*d*c-g*u3*c)*r)
   .exact mul_left_cancel₀ t (by linear_combination (j*k*a-h*k*c)*o+(-g*k*a+e*k*c)*p+(-j*m*a+h*m*c)*q+(g*m*a-e*m*c)*r)
   .exact mul_left_cancel₀ t (by linear_combination (-i*k*a+h*k*b)*o+(f*k*a-e*k*b)*p+(-h*d*a-j*u3*a-h*m*b)*q+(e*d*a+g*u3*a+e*m*b)*r)
 .right;refine⟨?_,?_,?_⟩
  .exact mul_left_cancel₀ s (by linear_combination (-j*n*b+i*n*c)*o+(g*n*b-f*n*c)*p+(j*d*b-i*d*c)*q+(-g*d*b+f*d*c)*r)
  .exact mul_left_cancel₀ s (by linear_combination (j*n*a+i*k*c+j*l*c)*o+(-g*n*a-f*k*c-g*l*c)*p+(-j*d*a+h*d*c)*q+(g*d*a-e*d*c)*r)
  .exact mul_left_cancel₀ s (by linear_combination (-i*n*a-i*k*b-j*l*b)*o+(f*n*a+f*k*b+g*l*b)*p+(i*d*a-h*d*b)*q+(-f*d*a+e*d*b)*r)
def afJ (z y x0 a b:V4) (i:x0.x1=0) (j:z.x1=16) (g:mp B0 y B2 B3=0)
  (h:mp B0 y B2 b+ mp B0 y a B3=0) (c:mp x0 y B2 B3=0) (d:mp x0 y B2 b+ mp x0 y a B3=0)
  (e:mp z y B2 B3=0) (f:mp z y B2 b+ mp z y a B3=0):
  TI (fi y).x0 (fi y).x2 (fi y).x3 (fe a b y).x0 (fe a b y).x2 (fe a b y).x3 x0.x0 x0.x2 x0.x3 (32- z.x0) (16- z.x2) (16- z.x3) 16 11 11:=by
 apply Xq<;>simp only[mp,fi,fe,B0,B1,B2,B3]at *
 all_goals grind
def ak5 (z y x0 a b:V4) (i:x0.x2=0) (j:z.x2=16) (g:mp B0 y B2 B3=0)
  (h:mp B0 y B2 b+ mp B0 y a B3=0) (c:mp x0 y B2 B3=0) (d:mp x0 y B2 b+ mp x0 y a B3=0)
  (e:mp z y B2 B3=0) (f:mp z y B2 b+ mp z y a B3=0):
  TI (fi y).x0 (fi y).x1 (fi y).x3 (fe a b y).x0 (fe a b y).x1 (fe a b y).x3 x0.x0 x0.x1 x0.x3 (32- z.x0) (16- z.x1) (16- z.x3) 16 11 11:=by
 apply Xq<;>simp only[mp,fi,fe,B0,B1,B2,B3]at *
 all_goals grind
def afK (z y x1 a b:V4) (i:x1.x1=0) (j:y.x1=11) (c:mp z B1 B2 B3=0)
  (d:mp z B1 B2 b+ mp z B1 a B3=0) (e:mp z x1 B2 B3=0) (f:mp z x1 B2 b+ mp z x1 a B3=0)
  (g:mp z y B2 B3=0) (h:mp z y B2 b+ mp z y a B3=0):
  TI (fi z).x0 (fi z).x2 (fi z).x3 (fe a b z).x0 (fe a b z).x2 (fe a b z).x3 x1.x0 x1.x2 x1.x3 (11-2*y.x0) (11-2*y.x2) (11-2*y.x3) 11 11 11:=by
 apply Xq<;>simp only[mp,fi,fe,B0,B1,B2,B3]at *
 all_goals grind
def ak6 (z y x1 a b:V4) (i:x1.x2=0) (j:y.x2=11) (c:mp z B1 B2 B3=0)
  (d:mp z B1 B2 b+ mp z B1 a B3=0) (e:mp z x1 B2 B3=0) (f:mp z x1 B2 b+ mp z x1 a B3=0)
  (g:mp z y B2 B3=0) (h:mp z y B2 b+ mp z y a B3=0):
  TI (fi z).x0 (fi z).x1 (fi z).x3 (fe a b z).x0 (fe a b z).x1 (fe a b z).x3 x1.x0 x1.x1 x1.x3 (11- y.x0) (22- y.x1) (11- y.x3) 11 16 11:=by
 apply Xq<;>simp only[mp,fi,fe,B0,B1,B2,B3]at *
 all_goals grind
def MR (g h i a b c d e f:ℂ):ℂ:=g*(b*f- c*e)- h*(a*f- c*d)+ i*(a*e- b*d)
def Sf (d e f g h i j k l b c u3:ℂ) (m:d*b+ e*c+ f*u3=0)
  (n:g*b+ h*c+ i*u3=0) (o:j*b+ k*c+ l*u3=0):
  MR d e f g h i j k l=0\/(b=0/\c=0/\u3=0):=by
 by_cases a:MR d e f g h i j k l=0
 .exact Or.inl a
 right;refine⟨(A0.1 ?_).resolve_left a,(A0.1 ?_).resolve_left a,(A0.1 ?_).resolve_left a⟩<;>unfold MR
 all_goals grind
def abJ (z x0 x1:V4) (g:x0.x1=0) (b:z.x1=16) (e:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (f:mp x0 x1 B2 B3=0) (a:mp z B1 B2 B3=0) (c:mp z x1 B2 B3=0)
  (s:WY x0.x0 x0.x2 x0.x3 (32- z.x0) (16- z.x2) (16- z.x3) 16 11 11):x0.x0=0/\x0.x1=0/\x0.x2=0/\x0.x3=0:=by
 obtain⟨h,i,j⟩:=s;simp only[mp,B0,B1,B2,B3]at e f a c
 have d:16*x0.x0+11*x0.x2+11*x0.x3=0:=E6 G0 |>.1 (by linear_combination (1/16:ℂ)*((5*x1.x1+3*x1.x2+3*x1.x3)*h+(3*x1.x0+3*x1.x1+2*x1.x3)*i+(3*x1.x0+3*x1.x1+2*x1.x2)*j+(-2816*x0.x0-1936*x0.x2-1936*x0.x3-80*x1.x0*z.x0-55*x1.x0*z.x2-55*x1.x0*z.x3+4320*x1.x0-48*x1.x2*z.x0-33*x1.x2*z.x2-33*x1.x2*z.x3+2592*x1.x2-48*x1.x3*z.x0-33*x1.x3*z.x2-33*x1.x3*z.x3+2592*x1.x3)*g+(80*x0.x0*x1.x0+48*x0.x0*x1.x2+48*x0.x0*x1.x3+55*x0.x2*x1.x0+33*x0.x2*x1.x2+33*x0.x2*x1.x3+55*x0.x3*x1.x0+33*x0.x3*x1.x2+33*x0.x3*x1.x3)*b-(-16*z.x0-11*z.x2-11*z.x3+864)*f+(256*x0.x0+176*x0.x2+176*x0.x3)*e-(16*x0.x0+11*x0.x2+11*x0.x3)*c))
 exact⟨(A0.1 (show (1040:ℂ)*x0.x0=0 by linear_combination h+(32- z.x0)*d+(x0.x0)*a-(11*x0.x0)*b)).resolve_left (by norm_num),g,(A0.1 (show (1040:ℂ)*x0.x2=0 by linear_combination i+(16- z.x2)*d+(x0.x2)*a-(11*x0.x2)*b)).resolve_left (by norm_num),(A0.1 (show (1040:ℂ)*x0.x3=0 by linear_combination j+(16- z.x3)*d+(x0.x3)*a-(11*x0.x3)*b)).resolve_left (by norm_num)⟩
def ald (z x0 x1:V4) (g:x0.x2=0) (b:z.x2=16) (e:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (f:mp x0 x1 B2 B3=0) (a:mp z B1 B2 B3=0) (c:mp z x1 B2 B3=0)
  (s:WY x0.x0 x0.x1 x0.x3 (32- z.x0) (16- z.x1) (16- z.x3) 16 11 11):x0.x0=0/\x0.x1=0/\x0.x2=0/\x0.x3=0:=by
 obtain⟨h,i,j⟩:=s;simp only[mp,B0,B1,B2,B3]at e f a c
 have d:16*x0.x0+11*x0.x1+11*x0.x3=0:=E6 G0 |>.1 (by linear_combination (1/16:ℂ)*((5*x1.x1+3*x1.x2+3*x1.x3)*h+(5*x1.x0+3*x1.x2+3*x1.x3)*i+(3*x1.x0+3*x1.x1+2*x1.x2)*j+(-2816*x0.x0-1936*x0.x1-1936*x0.x3-48*x1.x0*z.x0-33*x1.x0*z.x1-33*x1.x0*z.x3+2592*x1.x0-48*x1.x1*z.x0-33*x1.x1*z.x1-33*x1.x1*z.x3+2592*x1.x1-32*x1.x3*z.x0-22*x1.x3*z.x1-22*x1.x3*z.x3+1728*x1.x3)*g+(48*x0.x0*x1.x0+48*x0.x0*x1.x1+32*x0.x0*x1.x3+33*x0.x1*x1.x0+33*x0.x1*x1.x1+22*x0.x1*x1.x3+33*x0.x3*x1.x0+33*x0.x3*x1.x1+22*x0.x3*x1.x3)*b-(-16*z.x0-11*z.x1-11*z.x3+864)*f+(256*x0.x0+176*x0.x1+176*x0.x3)*e-(16*x0.x0+11*x0.x1+11*x0.x3)*c))
 exact⟨(A0.1 (show (1040:ℂ)*x0.x0=0 by linear_combination h+(32- z.x0)*d+(x0.x0)*a-(11*x0.x0)*b)).resolve_left (by norm_num),(A0.1 (show (1040:ℂ)*x0.x1=0 by linear_combination i+(16- z.x1)*d+(x0.x1)*a-(11*x0.x1)*b)).resolve_left (by norm_num),g,(A0.1 (show (1040:ℂ)*x0.x3=0 by linear_combination j+(16- z.x3)*d+(x0.x3)*a-(11*x0.x3)*b)).resolve_left (by norm_num)⟩
def abK (y x0 x1:V4) (g:x1.x1=0) (b:y.x1=11) (e:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (f:mp x0 x1 B2 B3=0) (a:mp B0 y B2 B3=0) (c:mp x0 y B2 B3=0)
  (s:WY x1.x0 x1.x2 x1.x3 (11-2*y.x0) (11-2*y.x2) (11-2*y.x3) 11 11 11):x1.x0=0/\x1.x1=0/\x1.x2=0/\x1.x3=0:=by
 obtain⟨h,i,j⟩:=s;simp only[mp,B0,B1,B2,B3]at e f a c
 have d:11*x1.x0+11*x1.x2+11*x1.x3=0:=E6 G0 |>.1 (by linear_combination (1/11:ℂ)*((5*x0.x1+3*x0.x2+3*x0.x3)*h+(3*x0.x0+3*x0.x1+2*x0.x3)*i+(3*x0.x0+3*x0.x1+2*x0.x2)*j+(-110*x0.x0*y.x0-110*x0.x0*y.x2-110*x0.x0*y.x3+1815*x0.x0-66*x0.x2*y.x0-66*x0.x2*y.x2-66*x0.x2*y.x3+1089*x0.x2-66*x0.x3*y.x0-66*x0.x3*y.x2-66*x0.x3*y.x3+1089*x0.x3-1936*x1.x0-1936*x1.x2-1936*x1.x3)*g+(110*x0.x0*x1.x0+110*x0.x0*x1.x2+110*x0.x0*x1.x3+66*x0.x2*x1.x0+66*x0.x2*x1.x2+66*x0.x2*x1.x3+66*x0.x3*x1.x0+66*x0.x3*x1.x2+66*x0.x3*x1.x3)*b-(-22*y.x0-22*y.x2-22*y.x3+363)*f+(121*x1.x0+121*x1.x2+121*x1.x3)*e-(22*x1.x0+22*x1.x2+22*x1.x3)*c))
 exact⟨(A0.1 (show (715:ℂ)*x1.x0=0 by linear_combination h+(11-2*y.x0)*d+(2*x1.x0)*a-(32*x1.x0)*b)).resolve_left (by norm_num),g,(A0.1 (show (715:ℂ)*x1.x2=0 by linear_combination i+(11-2*y.x2)*d+(2*x1.x2)*a-(32*x1.x2)*b)).resolve_left (by norm_num),(A0.1 (show (715:ℂ)*x1.x3=0 by linear_combination j+(11-2*y.x3)*d+(2*x1.x3)*a-(32*x1.x3)*b)).resolve_left (by norm_num)⟩
def ale (y x0 x1:V4) (g:x1.x2=0) (b:y.x2=11) (e:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (f:mp x0 x1 B2 B3=0) (a:mp B0 y B2 B3=0) (c:mp x0 y B2 B3=0)
  (s:WY x1.x0 x1.x1 x1.x3 (11- y.x0) (22- y.x1) (11- y.x3) 11 16 11):x1.x0=0/\x1.x1=0/\x1.x2=0/\x1.x3=0:=by
 obtain⟨h,i,j⟩:=s;simp only[mp,B0,B1,B2,B3]at e f a c
 have d:11*x1.x0+16*x1.x1+11*x1.x3=0:=E6 G0 |>.1 (by linear_combination (1/11:ℂ)*((5*x0.x1+3*x0.x2+3*x0.x3)*h+(5*x0.x0+3*x0.x2+3*x0.x3)*i+(3*x0.x0+3*x0.x1+2*x0.x2)*j+(-33*x0.x0*y.x0-48*x0.x0*y.x1-33*x0.x0*y.x3+1782*x0.x0-33*x0.x1*y.x0-48*x0.x1*y.x1-33*x0.x1*y.x3+1782*x0.x1-22*x0.x3*y.x0-32*x0.x3*y.x1-22*x0.x3*y.x3+1188*x0.x3-1331*x1.x0-1936*x1.x1-1331*x1.x3)*g+(33*x0.x0*x1.x0+48*x0.x0*x1.x1+33*x0.x0*x1.x3+33*x0.x1*x1.x0+48*x0.x1*x1.x1+33*x0.x1*x1.x3+22*x0.x3*x1.x0+32*x0.x3*x1.x1+22*x0.x3*x1.x3)*b-(-11*y.x0-16*y.x1-11*y.x3+594)*f+(121*x1.x0+176*x1.x1+121*x1.x3)*e-(11*x1.x0+16*x1.x1+11*x1.x3)*c))
 exact⟨(A0.1 (show (715:ℂ)*x1.x0=0 by linear_combination h+(11- y.x0)*d+(x1.x0)*a-(11*x1.x0)*b)).resolve_left (by norm_num),(A0.1 (show (715:ℂ)*x1.x1=0 by linear_combination i+(22- y.x1)*d+(x1.x1)*a-(11*x1.x1)*b)).resolve_left (by norm_num),g,(A0.1 (show (715:ℂ)*x1.x3=0 by linear_combination j+(11- y.x3)*d+(x1.x3)*a-(11*x1.x3)*b)).resolve_left (by norm_num)⟩
def ak0 (y x0 x1 a b:V4) (k:x0.x1=0) (j:x1.x0=0/\x1.x1=0/\x1.x2=0/\x1.x3=0)
  (d:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (e:mp B0 x1 B2 b+ mp B0 x1 a B3+ mp x0 B1 B2 b+ mp x0 B1 a B3=0) (c:mp x0 y B2 B3=0):
  MR (fi y).x0 (fi y).x2 (fi y).x3 16 11 11 (fe a b B1).x0 (fe a b B1).x2 (fe a b B1).x3=0\/(x0.x0=0/\x0.x2=0/\x0.x3=0):=by
 obtain⟨f,g,h,i⟩:=j;apply Sf<;>simp only[mp,fi,fe,B0,B1,B2,B3,f,g,h,i]at d e c ⊢
 all_goals grind
def ak1 (y x0 x1 a b:V4) (k:x0.x2=0) (j:x1.x0=0/\x1.x1=0/\x1.x2=0/\x1.x3=0)
  (d:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (e:mp B0 x1 B2 b+ mp B0 x1 a B3+ mp x0 B1 B2 b+ mp x0 B1 a B3=0) (c:mp x0 y B2 B3=0):
  MR (fi y).x0 (fi y).x1 (fi y).x3 16 11 11 (fe a b B1).x0 (fe a b B1).x1 (fe a b B1).x3=0\/(x0.x0=0/\x0.x1=0/\x0.x3=0):=by
 obtain⟨f,g,h,i⟩:=j;apply Sf<;>simp only[mp,fi,fe,B0,B1,B2,B3,f,g,h,i]at d e c ⊢
 all_goals grind
def ak2 (z x0 x1 a b:V4) (k:x1.x1=0) (j:x0.x0=0/\x0.x1=0/\x0.x2=0/\x0.x3=0)
  (d:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (e:mp B0 x1 B2 b+ mp B0 x1 a B3+ mp x0 B1 B2 b+ mp x0 B1 a B3=0) (c:mp z x1 B2 B3=0):
  MR (fi z).x0 (fi z).x2 (fi z).x3 11 11 11 (fe a b B0).x0 (fe a b B0).x2 (fe a b B0).x3=0\/(x1.x0=0/\x1.x2=0/\x1.x3=0):=by
 obtain⟨f,g,h,i⟩:=j;apply Sf<;>simp only[mp,fi,fe,B0,B1,B2,B3,f,g,h,i]at d e c ⊢
 all_goals grind
def ak3 (z x0 x1 a b:V4) (k:x1.x2=0) (j:x0.x0=0/\x0.x1=0/\x0.x2=0/\x0.x3=0)
  (d:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0)
  (e:mp B0 x1 B2 b+ mp B0 x1 a B3+ mp x0 B1 B2 b+ mp x0 B1 a B3=0) (c:mp z x1 B2 B3=0):
  MR (fi z).x0 (fi z).x1 (fi z).x3 11 16 11 (fe a b B0).x0 (fe a b B0).x1 (fe a b B0).x3=0\/(x1.x0=0/\x1.x1=0/\x1.x3=0):=by
 obtain⟨f,g,h,i⟩:=j;apply Sf<;>simp only[mp,fi,fe,B0,B1,B2,B3,f,g,h,i]at d e c ⊢
 all_goals grind
def Qa (a b:V4): Prop :=a.x0=1/\a.x2=0/\a.x3=0/\b.x2=0/\b.x3=0/\b.x1+ a.x1*b.x0=0/\b.x0≠0
def Qb (a b:V4): Prop :=a.x0=1/\a.x1=0/\a.x3=0/\b.x1=0/\b.x3=0/\b.x2+ a.x2*b.x0=0/\b.x0≠0
def Qc (a b:V4): Prop :=a.x0=1/\a.x1=0/\a.x2=0/\b.x1=0/\b.x2=0/\b.x3+ a.x3*b.x0=0/\b.x0≠0
def Qd (a b:V4): Prop :=a.x0=0/\a.x1=1/\a.x3=0/\b.x0=0/\b.x3=0/\b.x2+ a.x2*b.x1=0/\b.x1≠0
def Qe (a b:V4): Prop :=a.x0=0/\a.x1=1/\a.x2=0/\b.x0=0/\b.x2=0/\b.x3+ a.x3*b.x1=0/\b.x1≠0
def Qg (a b:V4): Prop :=a.x0=0/\a.x1=0/\a.x2=1/\b.x0=0/\b.x1=0/\b.x3+ a.x3*b.x2=0/\b.x2≠0
def SG (a b:V4): Prop :=a.x0=0/\a.x1=0/\a.x2=0/\a.x3=1/\b.x0=0/\b.x1=0/\b.x2=0/\b.x3≠0
def Vd (a b:V4) (C:Pz a b) (D:AC a) (s:¬ (b.x0=0/\b.x1=0/\b.x2=0/\b.x3=0)):
  Qa a b\/Qb a b\/Qc a b\/Qd a b\/Qe a b\/Qg a b\/SG a b:=by
 obtain⟨G,g,c,a3⟩:=a;obtain⟨d,e,j,q⟩:=b;simp only[Pz,AC,Qa,Qb,Qc,Qd,Qe,Qg,SG]at *
 obtain⟨t,w,x,y,z,u⟩:=C;rcases D with rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,rfl⟩⟩⟩
 .have m:e= -(g*d):=by linear_combination t
  have n:j= -(c*d):=by grind
  have o:q= -(a3*d):=by grind
  subst m n o
  have i:d≠0:=λh=> s ⟨h,by simp[h],by simp[h],by simp[h]⟩
  have A:g*c=0:=(A0.1 (show (g*c)*d=0 by linear_combination (-1/2:ℂ)*y)).resolve_right i
  have B:g*a3=0:=(A0.1 (show (g*a3)*d=0 by linear_combination (-1/2:ℂ)*z)).resolve_right i
  have p:c*a3=0:=(A0.1 (show (c*a3)*d=0 by linear_combination (-1/2:ℂ)*u)).resolve_right i
  by_cases r:g=0
  .by_cases f:c=0
   .subst r f;right;right;left;exact⟨rfl,rfl,rfl,by ring,by ring,by ring,i⟩
   .have k:a3=0:=(A0.1 p).resolve_left f
    subst r k;right;left;exact⟨rfl,rfl,rfl,by ring,by ring,by ring,i⟩
  .have f:c=0:=(A0.1 A).resolve_left r;have k:a3=0:=(A0.1 B).resolve_left r
   subst f k;left;exact⟨rfl,rfl,rfl,by ring,by ring,by ring,i⟩
 .have l:d=0:=by linear_combination t
  have n:j= -(c*e):=by grind
  have o:q= -(a3*e):=by grind
  subst l n o
  have v:e≠0:=λh=> s ⟨rfl,h,by simp[h],by simp[h]⟩
  have p:c*a3=0:=(A0.1 (show (c*a3)*e=0 by linear_combination (-1/2:ℂ)*u)).resolve_right v
  by_cases f:c=0
  .subst f;right;right;right;right;left;exact⟨rfl,rfl,rfl,rfl,by ring,by ring,v⟩
  .have k:a3=0:=(A0.1 p).resolve_left f
   subst k;right;right;right;left;exact⟨rfl,rfl,rfl,rfl,by ring,by ring,v⟩
 .have l:d=0:=by linear_combination w
  have m:e=0:=by grind
  have o:q= -(a3*j):=by grind
  subst l m o
  have E:j≠0:=λh=> s ⟨rfl,rfl,h,by simp[h]⟩
  right;right;right;right;right;left;exact⟨rfl,rfl,rfl,rfl,rfl,by ring,E⟩
 .have l:d=0:=by linear_combination x
  have m:e=0:=by grind
  have n:j=0:=by grind
  subst l m n
  have F:q≠0:=λh=> s ⟨rfl,rfl,rfl,h⟩
  right;right;right;right;right;right;exact⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,F⟩
def ajw {e f d:ℂ} {x0 x1 a b:V4} (h:Mh (zv 1 e f) (yv 0 1 d) x0 x1 a b):Pz a b:=by
 obtain⟨⟨-,c,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,c20,-,-⟩,hv,-⟩:=h;simp only[Ri,me,lu,mh,mj,mp,zv,yv,B0,B1,B2,B3]at c c20 hv;simp only[Pz];refine⟨?_,?_,?_,?_,?_,?_⟩<;>grind
def aiR {z A y:ℂ} {x0 x1 a b:V4} (h:Mh (zv 1 z A) (yv 0 1 y) x0 x1 a b) (t:x0.x1=0)
  (s:x1.x2=0) (l:XC x0 x1) (v:AC a) (x:¬ (b.x0=0/\b.x1=0/\b.x2=0/\b.x3=0)):False:=by
 have w:=ajw h;obtain⟨⟨u,-,c2,o,-,p,-,-,q,r,-,c11,i,-,e,j,-,c,k,-,f,g,-⟩,-,-⟩:=h
 have n:(zv 1 z A).x1=16:=by simp[zv]
 have m:(yv 0 1 y).x2=11:=by simp[yv]
 have t0:=F5 (abJ _ _ _ t n c2 p e c) (afJ _ _ _ _ _ t n q r c11 i f g);have t1:=F5 (ale _ _ _ s m c2 p q c11) (ak6 _ _ _ _ _ s m e j c k f g);rcases t0 with t0 | t0<;>rcases t1 with t1 | t1
 .clear l c2 o p q c11 i e c k n m;rcases Vd a b w v x with B | B | B | B | B | B | B<;>simp only[Qa,Qb,Qc,Qd,Qe,Qg,SG,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at B t0 t1 u r j f g<;>grind
 .rcases ak0 _ _ _ _ _ t t1 c2 o c11 with d | d
  .clear l c2 o p q c11 i e c k n m t1;rcases Vd a b w v x with B | B | B | B | B | B | B<;>simp only[Qa,Qb,Qc,Qd,Qe,Qg,SG,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3,MR]at B t0 d u r j f g<;>grind
  .simp[XC,t1,d,t]at l
 .rcases ak3 _ _ _ _ _ s t0 c2 o c with d | d
  .clear l c2 o p q c11 i e c k n m t0;rcases Vd a b w v x with B | B | B | B | B | B | B<;>simp only[Qa,Qb,Qc,Qd,Qe,Qg,SG,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3,MR]at B t1 d u r j f g<;>grind
  .simp[XC,t0,d,s]at l
 .simp[XC,t0,t1]at l
def ajx {f d e:ℂ} {x0 x1 a b:V4} (h:Mh (zv 0 1 f) (yv 1 d e) x0 x1 a b):Pz a b:=by
 obtain⟨⟨-,c,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,c20,-,-⟩,hv,-⟩:=h;simp only[Ri,me,lu,mh,mj,mp,zv,yv,B0,B1,B2,B3]at c c20 hv;simp only[Pz];refine⟨?_,?_,?_,?_,?_,?_⟩<;>grind
def aiS {A y z:ℂ} {x0 x1 a b:V4} (h:Mh (zv 0 1 A) (yv 1 y z) x0 x1 a b) (t:x0.x2=0)
  (s:x1.x1=0) (l:XC x0 x1) (v:AC a) (x:¬ (b.x0=0/\b.x1=0/\b.x2=0/\b.x3=0)):False:=by
 have w:=ajx h;obtain⟨⟨u,-,c2,o,-,p,-,-,q,r,-,c11,i,-,e,j,-,c,k,-,f,g,-⟩,-,-⟩:=h
 have n:(zv 0 1 A).x2=16:=by simp[zv]
 have m:(yv 1 y z).x1=11:=by simp[yv]
 have t0:=F5 (ald _ _ _ t n c2 p e c) (ak5 _ _ _ _ _ t n q r c11 i f g);have t1:=F5 (abK _ _ _ s m c2 p q c11) (afK _ _ _ _ _ s m e j c k f g);rcases t0 with t0 | t0<;>rcases t1 with t1 | t1
 .clear l c2 o p q c11 i e c k n m;rcases Vd a b w v x with B | B | B | B | B | B | B<;>simp only[Qa,Qb,Qc,Qd,Qe,Qg,SG,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at B t0 t1 u r j f g<;>grind
 .rcases ak1 _ _ _ _ _ t t1 c2 o c11 with d | d
  .clear l c2 o p q c11 i e c k n m t1;rcases Vd a b w v x with B | B | B | B | B | B | B<;>simp only[Qa,Qb,Qc,Qd,Qe,Qg,SG,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3,MR]at B t0 d u r j f g<;>grind
  .simp[XC,t1,d,t]at l
 .rcases ak2 _ _ _ _ _ s t0 c2 o c with d | d
  .clear l c2 o p q c11 i e c k n m t0;rcases Vd a b w v x with B | B | B | B | B | B | B<;>simp only[Qa,Qb,Qc,Qd,Qe,Qg,SG,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3,MR]at B t1 d u r j f g<;>grind
  .simp[XC,t0,d,s]at l
 .simp[XC,t0,t1]at l
def aiT {za ya:ℂ} {x0 x1 a b:V4} (h:Mh (zv 0 1 za) (yv 0 1 ya) x0 x1 a b) (hz:x0.x2=0)
  (hy:x1.x2=0) (P:XC x0 x1) (y:AC a) (z:¬ (b.x0=0/\b.x1=0/\b.x2=0/\b.x3=0)):False:=by
 obtain⟨⟨J,k,K,L,-,M,-,-,N,O,A,c11,m,-,n,o,B,p,r,-,C,s,D⟩,⟨V,u,W,X,Y,v,Z,w3⟩,-⟩:=h
 have E:(a.x0*b.x1+ a.x1*b.x0=0/\a.x1*b.x2+ a.x2*b.x1=0/\a.x1*b.x3+ a.x3*b.x1=0):=by
  clear J K L M N O c11 m n o p r s P y z;simp only[me,lu,mh,mj,mp,zv,yv,B0,B1,B2,B3]at *
  refine⟨?_,?_,?_⟩<;>grind
 obtain⟨F,G,H⟩:=E;by_cases f:a.x1=0
 .clear P hz hy z K L M N A c11 m n B p r D V W X Y Z w3;simp only[mp,lu,zv,yv,B0,B1,B2,B3]at J k O o C s u v;rcases Sf (-(1+ ya)) 1 ya (-11*(1+ za)) 16 (16*za) 5 3 3 (a.x2*b.x3+ a.x3*b.x2) (a.x0*b.x3+ a.x3*b.x0) (a.x0*b.x2+ a.x2*b.x0)
   (by linear_combination (1/11:ℂ)*u) (by linear_combination v) (by linear_combination k-3*G-3*H-2*F) with Q | ⟨q1,q2,q3⟩
  .unfold MR at Q
   have zl:4102*za=4592*ya+810:=by grind
   rcases y with g | ⟨g,x | ⟨x,t | ⟨t,U⟩⟩⟩<;>grind
  .clear k u v;rcases y with g | ⟨g,x | ⟨x,t | ⟨t,U⟩⟩⟩
   .obtain⟨S,T,w,j⟩:=a;obtain⟨c,d,e,i⟩:=b;simp only at *;subst g f
    obtain rfl :d=0:=by grind
    obtain rfl :e= -(w*c):=by grind
    obtain rfl :i= -(j*c):=by grind
    have q:w*j*c=0:=by grind
    simp only[A0]at q;rcases q with (rfl | rfl) | rfl<;>grind
   .simp[f]at x
   .obtain⟨S,T,w,j⟩:=a;obtain⟨c,d,e,i⟩:=b;simp only at *;subst g f t
    obtain rfl :d=0:=by grind
    obtain rfl :c=0:=by grind
    obtain rfl :i= -(j*e):=by grind
    grind
   .obtain⟨S,T,w,j⟩:=a;obtain⟨c,d,e,i⟩:=b;simp only at *;subst g f t U
    obtain rfl :d=0:=by grind
    obtain rfl :c=0:=by grind
    obtain rfl :e=0:=by grind
    grind
 .obtain⟨c,d,e,i⟩:=b;simp only at *
  obtain⟨l,rfl⟩:∃ l,d=l*a.x1:=⟨d/a.x1,by field_simp⟩
  obtain rfl :c= -l*a.x0:=mul_left_cancel₀ f (by linear_combination F)
  obtain rfl :e= -l*a.x2:=mul_left_cancel₀ f (by linear_combination G)
  obtain rfl :i= -l*a.x3:=mul_left_cancel₀ f (by linear_combination H)
  have R:l≠0:=λh=> z ⟨by simp[h],by simp[h],by simp[h],by simp[h]⟩
  clear F G H A B D V W X Y Z w3 z y P K L M N c11 m n p r;simp only[mp,lu,zv,yv,B0,B1,B2,B3]at J k O o C s u v;rcases Sf (-(1+ ya)) 1 ya (-11*(1+ za)) 16 (16*za) 5 3 3 (a.x2*a.x3) (a.x0*a.x3) (a.x0*a.x2)
   (mul_left_cancel₀ R (by linear_combination (-1/22:ℂ)*u)) (mul_left_cancel₀ R (by linear_combination (-1/2:ℂ)*v))
   (mul_left_cancel₀ R (by linear_combination (-1/2:ℂ)*k)) with Q | ⟨q1,q2,q3⟩
  .unfold MR at Q
   have zl:4102*za=4592*ya+810:=by grind
   grind
  .simp only[A0]at q1 q2 q3;rcases q1 with q1 | q1<;>rcases q2 with q2 | q2<;>rcases q3 with q3 | q3<;>grind
def tq (a b p2 p3 p4 c:ℂ) (u v:V4):ℂ:=
 c*(u.x0*v.x1+ u.x1*v.x0)+ p4*(u.x0*v.x2+ u.x2*v.x0)+ p3*(u.x0*v.x3+ u.x3*v.x0)+
 p2*(u.x1*v.x2+ u.x2*v.x1)+ b*(u.x1*v.x3+ u.x3*v.x1)+ a*(u.x2*v.x3+ u.x3*v.x2)
def apm (a b f g c d p2 p3 p4 e:ℂ) (q:11*e+11*f*p4+11*g*p3=0)
  (r: -(16+11*f+11*g)*e+11*f*p2+11*g*d=0)
  (s: -(16+11*f+11*g)*p4+11*p2+11*g*c=0)
  (t: -(16+11*f+11*g)*p3+11*d+11*f*c=0) (u:16*e+16*a*p4+16*b*p3=0)
  (v: -11*(1+ a+ b)*e+16*a*p2+16*b*d=0)
  (w: -11*(1+ a+ b)*p4+16*p2+16*b*c=0)
  (x: -11*(1+ a+ b)*p3+16*d+16*a*c=0)
  (p:2*c+3*d+3*p2+3*p3+3*p4+5*e=0) (k:mp (zv 1 a b) (yv 1 f g) B2 B3=0):
  (c=0/\d=0/\p2=0/\p3=0/\p4=0/\e=0)\/
  (c≠0/\p2=0/\p4=0/\e=0/\b=0/\g=0)\/
  (c≠0/\d=0/\p4=0/\g=b/\p2+ b*c=0/\e+ b*p3=0)\/
  (c≠0/\d=0/\p3=0/\e=0/\a=0/\f=0)\/
  (c≠0/\p2=0/\p3=0/\f=a/\d+ a*c=0/\e+ a*p4=0)\/
  (c=0/\d≠0/\e=0/\b=a/\g=f)\/
  (c=0/\d≠0/\e=0/\f=a/\g=b/\11*a+11*b+27=0/\22*a*b=107)\/
  (c=0/\d=0/\p2=0/\p3≠0/\1+ a+ b=0/\16+11*f+11*g=0):=by
 simp only[mp,zv,yv,B2,B3]at k;by_cases h:c=0
 .by_cases i:d=0
  .by_cases j:p2=0
   .by_cases o:p3=0
    .exact Or.inl ⟨h,i,j,o,by grind,by grind⟩
    .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h,i,j,o,by grind,by grind⟩))))))
   .exact absurd j (by grind)
  .have n:e=0:=by grind
   rcases A0.1 (show (a- b)*(a- f)=0 by grind) with hs | hs
   .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h,i,n,by grind,by grind⟩)))))
   .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h,i,n,by grind,by grind,by grind,by grind⟩))))))
 .rcases A0.1 (show p3*p4=0 by grind) with m | e4<;>rcases A0.1 (show d*p2=0 by grind) with l | e2
  .exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h,l,m,by grind,by grind,by grind⟩)))
  .exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h,e2,m,by grind,by grind,by grind⟩))))
  .exact Or.inr (Or.inr (Or.inl ⟨h,l,e4,by grind,by grind,by grind⟩))
  .exact Or.inr (Or.inl ⟨h,e2,e4,by grind,by grind,by grind⟩)
def akY {c a f b d g p2 p3 p4 e:ℂ} {x0 x1:V4} (p:x0.x1=0) (o:x1.x1=0) (m:XC x0 x1)
  (x:11*e+11*f*p4+11*b*p3=0)
  (y: -(16+11*f+11*b)*e+11*f*p2+11*b*g=0)
  (z: -(16+11*f+11*b)*p4+11*p2+11*b*d=0)
  (A: -(16+11*f+11*b)*p3+11*g+11*f*d=0) (B:16*e+16*c*p4+16*a*p3=0)
  (C: -11*(1+ c+ a)*e+16*c*p2+16*a*g=0)
  (D: -11*(1+ c+ a)*p4+16*p2+16*a*d=0)
  (E: -11*(1+ c+ a)*p3+16*g+16*c*d=0)
  (r:2*d+3*g+3*p2+3*p3+3*p4+5*e=0)
  (t:tq d g p2 p3 p4 e B0 x1+ tq d g p2 p3 p4 e x0 B1=0) (c7:tq d g p2 p3 p4 e x0 x1=0)
  (s:mp B0 x1 B2 B3+ mp x0 B1 B2 B3=0) (u:mp x0 x1 B2 B3=0) (k:mp x0 (yv 1 f b) B2 B3=0)
  (l:mp (zv 1 c a) x1 B2 B3=0) (c20:mp (zv 1 c a) (yv 1 f b) B2 B3=0):
  d=0/\g=0/\p2=0/\p3=0/\p4=0/\e=0:=by
 rcases apm c a f b d g p2 p3 p4 e x y z A B C D E r c20 with H | H | H | H | H | H | H | H
 .exact H
 all_goals exfalso;obtain⟨F,G,J,K⟩:=x0;obtain⟨L,M,N,O⟩:=x1
 all_goals simp only[XC,tq,mp,zv,yv,B0,B1,B2,B3]at p o m t c7 s u k l c20;subst p o
 on_goal 1=> obtain⟨n,rfl,rfl,rfl,rfl,rfl⟩:=H
 on_goal 2=> obtain⟨n,rfl,rfl,Q,j,v⟩:=H;subst b;obtain rfl :p2= -(a*d):=(by linear_combination j);obtain rfl :e= -(a*p3):=by grind
 on_goal 3=> obtain⟨n,rfl,rfl,rfl,rfl,rfl⟩:=H
 on_goal 4=> obtain⟨n,rfl,rfl,P,i,v⟩:=H;subst f;obtain rfl :g= -(c*d):=(by linear_combination i);obtain rfl :e= -(c*p4):=by grind
 on_goal 5=> obtain⟨rfl,n,rfl,i,j⟩:=H;subst a b
 on_goal 6=> obtain⟨rfl,n,rfl,i,j,q,w⟩:=H;subst f b;obtain rfl :a= -27/11- c:=by grind
 on_goal 7=> obtain⟨rfl,rfl,rfl,n,q,w⟩:=H;obtain rfl :a= -1- c:=(by linear_combination q);obtain rfl :b= -16/11- f:=by grind
 all_goals rcases m with rfl | ⟨rfl,h | ⟨-,rfl | ⟨rfl,rfl | ⟨rfl,rfl | ⟨rfl,h | ⟨-,rfl | ⟨rfl,rfl⟩⟩⟩⟩⟩⟩⟩<;>grind
def BK (a b:V4): Prop :=Qa a b\/Qb a b\/Qc a b\/Qd a b\/Qe a b\/Qg a b\/SG a b
def PQ (u v:V4): Prop :=Ma u.x0 u.x2 u.x3 v.x0 v.x2 v.x3
def sB0 (z y x1 a b:V4) (h:x1.x1=0) (i:y.x1=11) (f:mp B0 B1 B2 b+ mp B0 B1 a B3=0)
  (g:mp B0 y B2 b+ mp B0 y a B3=0) (j:mp B0 x1 B2 b+ mp B0 x1 a B3=0) (c:mp z B1 B2 B3=0)
  (d:mp z x1 B2 B3=0) (e:mp z y B2 B3=0):
  TI (fi z).x0 (fi z).x2 (fi z).x3 (fe a b B0).x0 (fe a b B0).x2 (fe a b B0).x3 x1.x0 x1.x2 x1.x3 (11-2*y.x0) (11-2*y.x2) (11-2*y.x3) 11 11 11:=by
 apply Xq<;>simp only[mp,fi,fe,B0,B1,B2,B3]at * <;>grind
def sB1 (z y x0 a b:V4) (h:x0.x1=0) (i:z.x1=16) (f:mp B0 B1 B2 b+ mp B0 B1 a B3=0)
  (d:mp z B1 B2 b+ mp z B1 a B3=0) (j:mp x0 B1 B2 b+ mp x0 B1 a B3=0) (g:mp B0 y B2 B3=0)
  (c:mp x0 y B2 B3=0) (e:mp z y B2 B3=0):
  TI (fi y).x0 (fi y).x2 (fi y).x3 (fe a b B1).x0 (fe a b B1).x2 (fe a b B1).x3 x0.x0 x0.x2 x0.x3 (32- z.x0) (16- z.x2) (16- z.x3) 16 11 11:=by
 apply Xq<;>simp only[mp,fi,fe,B0,B1,B2,B3]at * <;>grind
def kZ {za c:ℂ} {a b:V4} (B:BK a b) (d:PQ (fi (zv 1 za c)) (fe a b B0)) (t:PQ (fi (zv 1 za c)) (fe a b (zv 1 za c)))
  (c15:mp (zv 1 za c) B1 B2 b+ mp (zv 1 za c) B1 a B3=0) (m:mp B0 B1 B2 b+ mp B0 B1 a B3=0):False:=by
 obtain⟨e,f,g,h⟩:=a;obtain⟨i,j,k,l⟩:=b;simp only[BK,Qa,Qb,Qc,Qd,Qe,Qg,SG,PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at *
 rcases B with B | B | B | B | B | B | B<;>(casesm*_/\_;subst_vars;grind (ringSteps:=5000))
def kY {ya c:ℂ} {a b:V4} (B:BK a b) (d:PQ (fi (yv 1 ya c)) (fe a b B1)) (t:PQ (fi (yv 1 ya c)) (fe a b (yv 1 ya c)))
  (m:mp B0 (yv 1 ya c) B2 b+ mp B0 (yv 1 ya c) a B3=0) (l:mp B0 B1 B2 b+ mp B0 B1 a B3=0):False:=by
 obtain⟨a0,e,f,g⟩:=a;obtain⟨h,i,j,k⟩:=b;simp only[BK,Qa,Qb,Qc,Qd,Qe,Qg,SG,PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at *
 rcases B with B | B | B | B | B | B | B<;>(casesm*_/\_;subst_vars;grind (ringSteps:=5000))
def ad (v:V4):V4:=⟨18*v.x0-8*v.x1-15*v.x2-15*v.x3,-8*v.x0+18*v.x1-15*v.x2-15*v.x3,
 -15*v.x0-15*v.x1+45*v.x2-20*v.x3,-15*v.x0-15*v.x1-20*v.x2+45*v.x3⟩
def kw (a b u:V4):V4:=ad (fe a b u)
def kq (a b g u:V4):ℂ:=mp g (kw a b u) B2 B3
def KD (a b c d e v:V4):ℂ:=MR (kq a b c v) (kq a b d v) (kq a b e v) (kq a b c (kw a b v)) (kq a b d (kw a b v))
 (kq a b e (kw a b v)) (kq a b c (kw a b (kw a b v))) (kq a b d (kw a b (kw a b v))) (kq a b e (kw a b (kw a b v)))
def KY (a b:V4):ℂ:=KD a b ⟨-16,11,0,0⟩ ⟨-11,0,11,0⟩ ⟨-11,0,0,11⟩ B0
def KZ (a b:V4):ℂ:=KD a b ⟨-11,16,0,0⟩ ⟨-11,0,16,0⟩ ⟨-11,0,0,16⟩ B1
def pv (a b c d e f g v2 i j c2 l k:ℂ) (t:Ma a b c d e f) (h:a*g+ b*v2+ c*i=0)
  (m:j*a+ c2*b+ l*c=k) (n:k≠0):d*g+ e*v2+ f*i=0:=by
 obtain⟨o,p,q⟩:=t;refine (A0.1 ?_).resolve_left n;rw[<- m];grind
def kr {a b y c d g2 v:V4} {p q:ℂ} (e:∀ w,mp y w B2 B3=mp c w B2 B3+ p*mp d w B2 B3+ q*mp g2 w B2 B3)
  (hv:mp y v B2 b+ mp y v a B3=0) (L:∀ w,mp y w B2 B3=0->mp y w B2 b+ mp y w a B3=0):
  KD a b c d g2 v=0:=by
 have f:∀ u,mp y (kw a b u) B2 B3= -130*(mp y u B2 b+ mp y u a B3):=λu=> by
  simp only[kw,ad,fe,mp,B2,B3];ring
 have g:mp y (kw a b v) B2 B3=0:=by rw[f,hv,C3]
 have i:mp y (kw a b (kw a b v)) B2 B3=0:=by rw[f,L _ g,C3]
 have j:mp y (kw a b (kw a b (kw a b v))) B2 B3=0:=by rw[f,L _ i,C3]
 have r:∀ w,mp y w B2 B3=0->mp c w B2 B3*1+ mp d w B2 B3*p+ mp g2 w B2 B3*q=0:=λw h=> by
  rw[e]at h;grind
 rcases Sf _ _ _ _ _ _ _ _ _ 1 p q (r _ g) (r _ i) (r _ j) with h | h
 .exact h
 .exact absurd h.1 A7
def ky {ya c:ℂ} {a b:V4} (t:PQ (fi (yv 1 ya c)) (fe a b (yv 1 ya c))) (d:mp B0 (yv 1 ya c) B2 b+ mp B0 (yv 1 ya c) a B3=0):KY a b=0:=
 kr (y:=(yv 1 ya c)) (p:=ya) (q:=c) (λw=> by simp only[mp,yv];ring) (by simp only[mp]at d ⊢;linear_combination d) λw h=> by
  have :=pv _ _ _ _ _ _ (w.x0-2*w.x1) (w.x2- w.x1) (w.x3- w.x1) 4 3 3 130 t
   (by simp only[fi,mp,yv,B2,B3]at h ⊢;linear_combination h) (by simp only[fi,yv];ring) (by norm_num)
  simp only[fe,mp,yv,B0,B2,B3]at this d ⊢;grind
def kz {za c:ℂ} {a b:V4} (t:PQ (fi (zv 1 za c)) (fe a b (zv 1 za c))) (d:mp (zv 1 za c) B1 B2 b+ mp (zv 1 za c) B1 a B3=0):KZ a b=0:=
 kr (y:=(zv 1 za c)) (p:=za) (q:=c) (λw=> by simp only[mp,zv];ring) d λw h=> by
  have :=pv _ _ _ _ _ _ (w.x0- w.x1/2) (w.x2- w.x1/2) (w.x3- w.x1/2) 17 24 24 2080 t
   (by simp only[fi,mp,zv,B2,B3]at h ⊢;linear_combination h) (by simp only[fi,zv];ring) (by norm_num)
  simp only[fe,mp,zv,B1,B2,B3]at this d ⊢;grind
def Hs (a b:P1):P2->P1
 | []=>[]
 | f::g=> Ry (oz f (Nq b g.length)) (oz (oz [-1] a) (Hs a b g))
lemma adh (a b:P1) (s l:ℂ) (h:gn s a+ l*gn s b=0):
  ∀ F:P2,gn s (Hs a b F)=gn s b^(F.length-1)*ly s l F
 | []=> by simp[Hs,gn,ly,ld]
 | [f]=> by
  have e1:=Sb s (oz f (Nq b 0)) (oz (oz [-1] a) []);simp only[Hs,List.length_nil,List.length_singleton,Nat.sub_self,pow_zero,G8]at e1 ⊢;rw[e1,Lj,Lj,Rz];simp[gn,ly,ld]
 | f::g::F=> by
  have c:=adh a b s l h (g::F);have e1:=Sb s (oz f (Nq b (g::F).length)) (oz (oz [-1] a) (Hs a b (g::F)))
  have d:gn s [-1]= -1:=by simp[gn,ld]
  have e:ly s l (f::g::F)=gn s f+ l*ly s l (g::F):=rfl;rw[Hs];simp only[List.length_cons,Nat.add_sub_cancel]at c e1 ⊢;rw[e1,Lj,Lj,Lj,Rz,c,d,e,pow_succ];grind
def Xz:List (ℤ× ℤ)->P1
 | []=>[1]
 | q::L=> oz [-q.1,q.2] (Xz L)
lemma aeq (s:ℂ):∀ L:List (ℤ× ℤ),gn s (Xz L)=0-> ∃ q∈L,(q.2:ℂ)*s=q.1
 | [],h=> by simp[Xz,gn,ld]at h
 | q::L,h=> by
  rw[Xz,Lj]at h;rcases A0.1 h with h | h
  .exact⟨q,List.mem_cons_self ..,by simp[gn,ld]at h;linear_combination h⟩
  .obtain⟨b,a,e⟩:=aeq s L h;exact⟨b,List.mem_cons_of_mem _ a,e⟩
def k2e (R0 a:P1) (L:List (ℤ× ℤ)):Bool:=
 match YE R0 a with
 | (S,T,g)=> match Zqt (Xz L) g with
  | (H,c)=> c !=0 && Rz1 (Ry (Ry (oz S R0) (oz T a)) (oz [-1] g)) && Rz1 (Ry (oz [(c:ℤ)] (Xz L)) (oz [-1] (oz H g)))
def k2s (F G C:P2) (L:List (ℤ× ℤ))
  (hk:(decide (C.length≤2) && k2e (Hs (C.getD 0 []) (C.getD 1 []) F) (Hs (C.getD 0 []) (C.getD 1 []) G) L)=true)
  (s l:ℂ) (i:ly s l F=0) (j:ly s l G=0) (e:ly s l C=0):∃ q∈L,(q.2:ℂ)*s=q.1:=by
 simp only[D8,N5]at hk;obtain⟨hn,hk⟩:=hk
 have hab:gn s (C.getD 0 [])+ l*gn s (C.getD 1 [])=0:=by
  rcases C with _ | ⟨a,_ | ⟨b,_ | ⟨c,C⟩⟩⟩
  .simp[gn,ld]
  .simpa[ly,gn,ld] using e
  .simpa[ly,ld] using e
  .simp at hn
 unfold k2e at hk;generalize YE (Hs (C.getD 0 []) (C.getD 1 []) F) (Hs (C.getD 0 []) (C.getD 1 []) G)=t at hk;rcases t with⟨S,T,g⟩;simp only[D8,L4,D7]at hk;obtain⟨⟨k,m⟩,o⟩:=hk
 have d:gn s [-1]= -1:=by simp[gn,ld]
 have h:∀ n:ℕ,gn s [(n:ℤ)]=(n:ℂ):=by intro n;simp[gn,ld]
 have f:=aaY s _ m;rw[Sb s,Sb s,Lj,Lj,Lj,adh _ _ s l hab,adh _ _ s l hab,i,j,d]at f;have y2:=aaY s _ o
 rw[Sb s,Lj,Lj,Lj,d,h,show gn s g=0 by linear_combination -f]at y2
 exact aeq s L ((A0.1 (show ((Zqt (Xz L) g).2:ℂ)*gn s (Xz L)=0 by linear_combination y2)).resolve_left (by exact_mod_cast k))
structure W4 where
 x0:P2
 x1:P2
 x2:P2
 x3:P2
def KH (s l:ℂ) (w:W4):V4:=⟨ly s l w.x0,ly s l w.x1,ly s l w.x2,ly s l w.x3⟩
def cW (a b c d:ℤ):W4:=⟨[[a]],[[b]],[[c]],[[d]]⟩
def OY (a b c d:ℤ) (v:W4):P2:=Lo (Lo (Il [[a]] v.x0) (Il [[b]] v.x1)) (Lo (Il [[c]] v.x2) (Il [[d]] v.x3))
def prS (p q r x y z:P2):P2:=Lo (Lo (Il p x) (Il q y)) (Il r z)
def PW (x y z w:P2):P2:=Lo (Il x y) (Il z w)
def adW (v:W4):W4:=⟨OY 18 (-8) (-15) (-15) v,OY (-8) 18 (-15) (-15) v,OY (-15) (-15) 45 (-20) v,OY (-15) (-15) (-20) 45 v⟩
def lmS (a b u:W4):W4:=
 let p:=Lo (OY 0 0 2 1 a) (OY 0 0 1 2 b);let q:=Lo (OY 0 2 0 1 a) (OY 0 1 0 1 b);let r:=Lo (OY 0 1 1 0 a) (OY 0 2 1 0 b)
 let x:=Lo (OY 2 0 0 1 a) (OY 1 0 0 1 b);let y:=Lo (OY 1 0 1 0 a) (OY 2 0 1 0 b);let z:=Lo (OY 1 1 0 0 a) (OY 1 1 0 0 b)
 ⟨prS p q r u.x1 u.x2 u.x3,prS p x y u.x0 u.x2 u.x3,prS q x z u.x0 u.x1 u.x3,prS r y z u.x0 u.x1 u.x2⟩
def mpS (a b c d:W4):P2:=
 Lo (Lo (Lo (Il (PW a.x0 b.x1 a.x1 b.x0) (PW c.x2 d.x3 c.x3 d.x2)) (Il (PW a.x0 b.x2 a.x2 b.x0) (PW c.x1 d.x3 c.x3 d.x1)))
  (Lo (Il (PW a.x0 b.x3 a.x3 b.x0) (PW c.x1 d.x2 c.x2 d.x1)) (Il (PW a.x1 b.x2 a.x2 b.x1) (PW c.x0 d.x3 c.x3 d.x0))))
  (Lo (Il (PW a.x1 b.x3 a.x3 b.x1) (PW c.x0 d.x2 c.x2 d.x0)) (Il (PW a.x2 b.x3 a.x3 b.x2) (PW c.x0 d.x1 c.x1 d.x0)))
def dtS (g h i a b c d e f:P2):P2:=
 Lo (Lo (Il g (PW b f [[-1]] (Il c e))) (Il [[-1]] (Il h (PW a f [[-1]] (Il c d))))) (Il i (PW a e [[-1]] (Il b d)))
def Td (a b u:W4):W4:=adW (lmS a b u)
def U7 (a b g u:W4):P2:=mpS g (Td a b u) (cW 1 1 2 1) (cW 1 1 1 2)
def KXS (a b c d e v:W4):P2:=
 dtS (U7 a b c v) (U7 a b d v) (U7 a b e v) (U7 a b c (Td a b v)) (U7 a b d (Td a b v)) (U7 a b e (Td a b v))
  (U7 a b c (Td a b (Td a b v))) (U7 a b d (Td a b (Td a b v))) (U7 a b e (Td a b (Td a b v)))
def YJ (a b:W4):P2:=Lo (mpS (cW 2 1 1 1) (cW 1 2 1 1) (cW 1 1 2 1) b) (mpS (cW 2 1 1 1) (cW 1 2 1 1) a (cW 1 1 1 2))
def aj0 (s l:ℂ) (a b:W4):ly s l (KXS a b (cW (-16) 11 0 0) (cW (-11) 0 11 0) (cW (-11) 0 0 11) (cW 2 1 1 1))=KY (KH s l a) (KH s l b)/\
  ly s l (KXS a b (cW (-11) 16 0 0) (cW (-11) 0 16 0) (cW (-11) 0 0 16) (cW 1 2 1 1))=KZ (KH s l a) (KH s l b)/\
  ly s l (YJ a b)=mp B0 B1 B2 (KH s l b)+ mp B0 B1 (KH s l a) B3:=by
 have e:=aaZ s l;have f:=aes s l
 have q:∀ k:ℤ,ly s l [[k]]=k:=by intro k;simp[ly,gn,ld]
 have w:∀ a b c d:ℤ,KH s l (cW a b c d)=⟨a,b,c,d⟩:=by intro a b c d;simp only[KH,cW,q]
 have t:∀ (a b c d:ℤ) (v:W4),ly s l (OY a b c d v)=a*(KH s l v).x0+ b*(KH s l v).x1+ c*(KH s l v).x2+ d*(KH s l v).x3:=by
  intro a b c d v;simp only[OY,e,f,q,KH];ring
 have hv:∀ a b u:W4,KH s l (Td a b u)=kw (KH s l a) (KH s l b) (KH s l u):=by
  intro a b u;simp only[Td,kw,adW,lmS,ad,fe,KH,prS,e,f,t,V4.mk.injEq];refine⟨?_,?_,?_,?_⟩<;>push_cast<;>ring
 have hp:∀ a b c d:W4,ly s l (mpS a b c d)=mp (KH s l a) (KH s l b) (KH s l c) (KH s l d):=by
  intro a b c d;simp only[mpS,mp,PW,e,f,KH];ring
 have r:∀ g h i j b2 m n o p:P2,ly s l (dtS g h i j b2 m n o p)=
   MR (ly s l g) (ly s l h) (ly s l i) (ly s l j) (ly s l b2) (ly s l m) (ly s l n) (ly s l o) (ly s l p):=by
  intro g h i j b2 m n o p;simp only[dtS,PW,MR,e,f,q];push_cast;ring
 refine⟨?_,?_,?_⟩<;>simp only[KXS,KY,KZ,kq,U7,YJ,r,hp,hv,w,e,KD,B0,B1,B2,B3]<;>push_cast<;>rfl
def Zu (a b:W4) (L:List (ℤ× ℤ)) (i:(decide ((YJ a b).length≤2) && k2e (Hs ((YJ a b).getD 0 []) ((YJ a b).getD 1 [])
  (KXS a b (cW (-16) 11 0 0) (cW (-11) 0 11 0) (cW (-11) 0 0 11) (cW 2 1 1 1))) (Hs ((YJ a b).getD 0 []) ((YJ a b).getD 1 [])
  (KXS a b (cW (-11) 16 0 0) (cW (-11) 0 16 0) (cW (-11) 0 0 16) (cW 1 2 1 1))) L)=true) (s l:ℂ) (u v:V4)
  (j:KH s l a=u) (hv:KH s l b=v) (f:KY u v=0) (g:KZ u v=0) (h:mp B0 B1 B2 v+ mp B0 B1 u B3=0):
  ∃ q∈L,(q.2:ℂ)*s=q.1:=by
 subst j hv;obtain⟨c,d,e⟩:=aj0 s l a b;exact k2s _ _ _ L i s l (c.trans f) (d.trans g) (e.trans h)
def EV (a b u:V4) (r:ℂ): Prop :=5*(fe a b u).x0+ r*(fi u).x0=0/\5*(fe a b u).x1+ r*(fi u).x1=0/\
 5*(fe a b u).x2+ r*(fi u).x2=0/\5*(fe a b u).x3+ r*(fi u).x3=0
lemma ey {s l a b:ℂ} (t:PQ (fi (yv 1 a b)) (fe ⟨0,0,1,s⟩ ⟨0,0,l,-(s*l)⟩ (yv 1 a b))) (d:mp B0 (yv 1 a b) B2 ⟨0,0,l,-(s*l)⟩+ mp B0 (yv 1 a b) ⟨0,0,1,s⟩ B3=0)
  (c:11*a+11*b+27≠0):EV ⟨0,0,1,s⟩ ⟨0,0,l,-(s*l)⟩ (yv 1 a b) (2*l*s- l- s-2):=by
 obtain⟨e,f,g⟩:=t;simp only[EV,fi,fe,mp,yv,B0,B2,B3]at *
 refine⟨?_,?_,?_,?_⟩<;>refine (A0.1 ?_).resolve_left c
 all_goals grind
lemma ez {s l a b:ℂ} (t:PQ (fi (zv 1 a b)) (fe ⟨0,0,1,s⟩ ⟨0,0,l,-(s*l)⟩ (zv 1 a b))) (d:mp (zv 1 a b) B1 B2 ⟨0,0,l,-(s*l)⟩+ mp (zv 1 a b) B1 ⟨0,0,1,s⟩ B3=0)
  (c:11*a+11*b+27≠0):EV ⟨0,0,1,s⟩ ⟨0,0,l,-(s*l)⟩ (zv 1 a b) (2*l*s- l- s-2):=by
 obtain⟨e,f,g⟩:=t;simp only[EV,fi,fe,mp,zv,B1,B2,B3]at *
 refine⟨?_,?_,?_,?_⟩<;>refine (A0.1 ?_).resolve_left c
 all_goals grind
def kX {n o ya m:ℂ} {a b:V4} (B:BK a b) (c:PQ (fi (yv 1 ya m)) (fe a b (yv 1 ya m))) (d:PQ (fi (zv 1 n o)) (fe a b (zv 1 n o)))
  (g:mp B0 B1 B2 b+ mp B0 B1 a B3=0) (c9:mp B0 (yv 1 ya m) B2 b+ mp B0 (yv 1 ya m) a B3=0) (c15:mp (zv 1 n o) B1 B2 b+ mp (zv 1 n o) B1 a B3=0)
  (i:mp (zv 1 n o) (yv 1 ya m) B2 B3=0) (j:mp (zv 1 n o) (yv 1 ya m) B2 b+ mp (zv 1 n o) (yv 1 ya m) a B3=0):False:=by
 rcases B with B | B | B | B | B | B | B
 on_goal 6=>
  obtain⟨r,a1,x,s⟩:=a;obtain⟨z,w,l,k⟩:=b
  simp only[Qg]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,h,t⟩:=B;obtain rfl :k= -(s*l):=by grind
  by_cases A:11*ya+11*m+27=0<;>by_cases C:11*n+11*o+27=0
  .simp only[PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at c d g c9 c15 i j;grind (ringSteps:=20000)
  .have e:=ez d c15 C;simp only[EV,PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at e c d g c9 c15 i j;grind (ringSteps:=5000)
  .have e:=ey c c9 A;simp only[EV,PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at e c d g c9 c15 i j;grind (ringSteps:=5000)
  .have e:=ey c c9 A;have f:=ez d c15 C;simp only[EV,PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at e f c d g c9 c15 i j;grind (ringSteps:=20000)
 on_goal 6=>
  obtain⟨r,a1,x,y⟩:=a;obtain⟨z,w,p,k⟩:=b
  simp only[SG]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,t⟩:=B
  obtain⟨-,u,v⟩:=c;simp only[PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at u v d g i j;grind (ringSteps:=5000)
 on_goal 1=> obtain⟨r,s,x,y⟩:=a;obtain⟨l,w,p,k⟩:=b;simp only[Qa]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,h,t⟩:=B;obtain rfl :w= -(s*l):=(by linear_combination h);obtain⟨q,hq,e⟩:=Zu ⟨[[1]],[[0,1]],[],[]⟩ ⟨[[],[1]],[[],[0,-1]],[],[]⟩ [(0,1),(1,1),(-1,1)] (by decide +kernel) s l _ _ (by simp[KH,ly,gn,ld]<;>ring) (by simp[KH,ly,gn,ld]<;>ring) (ky c c9) (kz d c15) g
 on_goal 2=> obtain⟨r,a1,s,y⟩:=a;obtain⟨l,w,p,k⟩:=b;simp only[Qb]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,h,t⟩:=B;obtain rfl :p= -(s*l):=(by linear_combination h);obtain⟨q,hq,e⟩:=Zu ⟨[[1]],[],[[0,1]],[]⟩ ⟨[[],[1]],[],[[],[0,-1]],[]⟩ [(0,1),(-11,43),(-22,5)] (by decide +kernel) s l _ _ (by simp[KH,ly,gn,ld]<;>ring) (by simp[KH,ly,gn,ld]<;>ring) (ky c c9) (kz d c15) g
 on_goal 3=> obtain⟨r,a1,x,s⟩:=a;obtain⟨l,w,p,k⟩:=b;simp only[Qc]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,h,t⟩:=B;obtain rfl :k= -(s*l):=(by linear_combination h);obtain⟨q,hq,e⟩:=Zu ⟨[[1]],[],[],[[0,1]]⟩ ⟨[[],[1]],[],[],[[],[0,-1]]⟩ [(11,43),(0,1),(22,5)] (by decide +kernel) s l _ _ (by simp[KH,ly,gn,ld]<;>ring) (by simp[KH,ly,gn,ld]<;>ring) (ky c c9) (kz d c15) g
 on_goal 4=> obtain⟨r,a1,s,y⟩:=a;obtain⟨z,l,p,k⟩:=b;simp only[Qd]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,h,t⟩:=B;obtain rfl :p= -(s*l):=(by linear_combination h);obtain⟨q,hq,e⟩:=Zu ⟨[],[[1]],[[0,1]],[]⟩ ⟨[],[[],[1]],[[],[0,-1]],[]⟩ [(0,1),(-11,43),(-22,5)] (by decide +kernel) s l _ _ (by simp[KH,ly,gn,ld]<;>ring) (by simp[KH,ly,gn,ld]<;>ring) (ky c c9) (kz d c15) g
 on_goal 5=> obtain⟨r,a1,x,s⟩:=a;obtain⟨z,l,p,k⟩:=b;simp only[Qe]at B;obtain⟨rfl,rfl,rfl,rfl,rfl,h,t⟩:=B;obtain rfl :k= -(s*l):=(by linear_combination h);obtain⟨q,hq,e⟩:=Zu ⟨[],[[1]],[],[[0,1]]⟩ ⟨[],[[],[1]],[],[[],[0,-1]]⟩ [(11,43),(0,1),(22,5)] (by decide +kernel) s l _ _ (by simp[KH,ly,gn,ld]<;>ring) (by simp[KH,ly,gn,ld]<;>ring) (ky c c9) (kz d c15) g
 all_goals simp at hq;rcases hq with rfl | rfl | rfl<;>norm_num at e<;>(simp only[PQ,Ma,fi,fe,mp,zv,yv,B0,B1,B2,B3]at c d g c9 c15 i j;grind (ringSteps:=5000))
def akT {H J F G:ℂ} (x0 x1 a b:V4)
  (S:Mh (zv 1 H J) (yv 1 F G) x0 x1 a b) (h:x0.x1=0) (g:x1.x1=0)
  (r:XC x0 x1) (U:AC a) (V:NZ b):False:=by
 obtain⟨⟨i,s,j,o,t,l,-,c7,p,q,-,c,D,-,e,f,-,d,E,-,c20,k,-⟩,⟨v,w,x,y,z,A,w2,C⟩,-⟩:=S
 have T:Pz a b:=by
  simp only[me,lu,mh,mj,mp,zv,yv,B0,B1]at v w x y z A w2 C s t c7
  exact akY h g r (by linear_combination v) (by linear_combination w) (by linear_combination x)
   (by linear_combination y) (by linear_combination z) (by linear_combination A) (by linear_combination w2)
   (by linear_combination C) (by linear_combination s) (by simp only[tq,B0,B1];linear_combination t)
   (by simp only[tq];linear_combination c7) j l c d c20
 clear s t c7 v w x y z A w2 C
 have n:(zv 1 H J).x1=16:=by simp[zv]
 have m:(yv 1 F G).x1=11:=by simp[yv]
 have t0:=F5 (abJ _ _ _ h n j l e d) (afJ _ _ _ _ _ h n p q c D c20 k);have t1:=F5 (abK _ _ _ g m j l p c) (afK _ _ _ _ _ g m e f d E c20 k);have B:=Vd a b T U V;rcases t0 with t0 | t0<;>rcases t1 with t1 | t1
 .exact kX B t0 t1 i q f c20 k
 .rcases F5 (abJ _ _ _ h n j l e d) (sB1 _ _ _ _ _ h n i f (by
   obtain⟨O,P,Q,R⟩:=t1;simp only[mp,O,P,Q,R]at o ⊢;linear_combination o) p c c20) with u | u
  .exact kY B u t0 q i
  .simp[XC,t1,u,h]at r
 .rcases F5 (abK _ _ _ g m j l p c) (sB0 _ _ _ _ _ g m i q (by
   obtain⟨K,L,M,N⟩:=t0;simp only[mp,K,L,M,N]at o ⊢;linear_combination o) e d c20) with u | u
  .exact kZ B u t1 f i
  .simp[XC,t0,u,g]at r
 .simp[XC,t0,t1]at r
def aiQ:abY:=by
 intro z y x0 x1 a b d i h f e g;rcases i with⟨⟨k,m,rfl⟩,h1⟩ | ⟨⟨k,rfl⟩,h1⟩ | ⟨rfl,h1⟩<;>
 rcases h with⟨⟨j,l,rfl⟩,c⟩ | ⟨⟨j,rfl⟩,c⟩ | ⟨rfl,c⟩
 .exact akT x0 x1 a b d h1 c f e g
 .exact aiR d h1 c f e g
 .exact akO x0 x1 a b d h1 c f e
 .exact aiS d h1 c f e g
 .exact aiT d h1 c f e g
 .exact akP x0 x1 a b d h1 c f e
 .exact akQ x0 x1 a b d h1 c f e
 .exact akR x0 x1 a b d h1 c f e
 .exact akS x0 x1 a b d h1 c f e
def apx:RE:=agU aiO aiQ
def Kl (c:Fq):Mt→ₗ[ℂ] (Fq->ℂ):=(af c).comp Mv
lemma Nt (c:Fq) (X:Mt) (i:Fq):Kl c X i=X (i,c):=rfl
def iu (L:Sq) (c:Fq):Sq:=L ⊓ ker (Kl c)
lemma ti (L:Sq) (c:Fq) (X:Mt):
  X∈iu L c↔X∈L/\ ∀ i,X (i,c)=0:=by
 unfold iu;rw[A6,C7];constructor
 .rintro⟨a,b⟩
  exact⟨a,λi=> by have :=congrFun b i;simpa[Nt] using this⟩
 .rintro⟨a,b⟩
  exact⟨a,by ext i;simp[Nt,b i]⟩
lemma KW (L:Sq) (a:Equiv.Perm Fq) (r:Fq):
  finrank ℂ ((L.map (gp a)).map (af r))=finrank ℂ (L.map (af (a.symm r))):=by
 rw[<- H8,ZD,H8,L6]
def ZM (r c:Fq):∃ b:Equiv.Perm (Fq),b r=0/\(b c).val<2:=by
 by_cases a:r=c
 .subst a;exact⟨swap r 0,by simp,by simp⟩
 .refine⟨swap (swap r 0 c) 1*swap r 0,?_,?_⟩
  .have d:swap r 0 c≠0:=by
    intro h;apply a;have :=congrArg (swap r 0) h;simp at this;exact this.symm
   simp only[Equiv.Perm.mul_apply,L9]
   rw[Equiv.swap_apply_of_ne_of_ne d.symm (by decide)]
  .simp
def p2 (M:Fin 2× Fin 2->ℂ):ℂ:=M (0,0)*M (1,1)+ M (0,1)*M (1,0)
def sw2:(Fin 2× Fin 2->ℂ)→ₗ[ℂ] (Fin 2× Fin 2->ℂ) where
 toFun y:=λq=> y (Fin.rev q.1,Fin.rev q.2)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def ajs (X y:Fin 2× Fin 2->ℂ):
  p2 (X+ y)=p2 X+ p2 y+ dotProduct X (sw2 y):=by
 simp[p2,sw2,dotProduct,N9,Fin.sum_univ_two];ring
def agp:Function.Injective sw2:=by
 intro a b h;funext q;have :=congrFun h (Fin.rev q.1,Fin.rev q.2);simpa[sw2] using this
def F2 (L:Submodule ℂ (Fin 2× Fin 2->ℂ)) (X0:Fin 2× Fin 2->ℂ)
  (c:∀ X∈L ⊔ span ℂ {X0},∀ y∈L,p2 (X+ y)=p2 X) (k:p2 X0≠0):
  finrank ℂ L≤1:=by
 have f:∀ y∈L,p2 y=0:=by
  intro y d;have :=c 0 (Submodule.zero_mem _) y d;rw[C0]at this;rw[this];simp[p2]
 have g:X0∉ L:=λh=> k (f X0 h)
 have aoE:∀ a∈L.map sw2,∀ b∈L ⊔ span ℂ {X0},dotProduct a b=0:=by
  intro a i b j;obtain⟨y,d,rfl⟩:=B6.1 i;have e:=ajs b y;rw[c b j y d,f y d]at e;rw[dotProduct_comm];grind
 have h1:=Sw _ _ aoE;have l:finrank ℂ (L.map sw2)=finrank ℂ L:=
  (K2 (equivMapOfInjective _ agp L)).symm
 have m:=du L X0 g;simp only[Fintype.card_prod,Fintype.card_fin]at h1;omega
def Li:(Ft× Ft->ℂ)→ₗ[ℂ] (Fin 2× Fin 2->ℂ) where
 toFun X:=λq=> X (q.1.succ,q.2.succ)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def Rq:(Ft× Ft->ℂ)→ₗ[ℂ] (Ft->ℂ) where
 toFun X:=λk=> X (0,k)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma aaI (c:ℂ) (M:Ft× Ft->ℂ):p3 (c•M)=c^3*p3 M:=by
 simp[p3];ring
def Zz (M:Ft× Ft->ℂ) (a:M (0,1)=0) (b:M (0,2)=0):
  p3 M=M (0,0)*p2 (Li M):=by
 simp[p3,p2,Li,a,b];ring
lemma acY (A B:Fin 2× Fin 2->ℂ):
  p2 A=3*p2 (A+(1:ℂ)•B)-3*p2 (A+(2:ℂ)•B)+ p2 (A+(3:ℂ)•B):=by
 simp[p2];ring
def afR (L:Submodule ℂ (Ft× Ft->ℂ)) (D:Ft× Ft->ℂ)
  (o:∀ X∈L ⊔ span ℂ {D},∀ y∈L,p3 (X+ y)=p3 X)
  (Xs:Ft× Ft->ℂ) (Y:Xs∈L ⊔ span ℂ {D})
  (s:Xs (0,0)=1) (Xk:Xs (0,1)=0) (Xl:Xs (0,2)=0) (W:p3 Xs≠0)
  (B:Ft× Ft->ℂ) (ae:B∈L ⊔ span ℂ {D})
  (ay:B (0,1)=1) (az:B (0,2)=0)
  (W2:Ft× Ft->ℂ) (ag:W2∈L ⊔ span ℂ {D})
  (aA:W2 (0,1)=0) (aB:W2 (0,2)=1):
  finrank ℂ L≤3:=by
 set C:=L ⊔ span ℂ {D} with hC;have aG:L≤ C:=K8;by_contra ap;push Not at ap;set K:=L ⊓ ker Rq with hK
 have aQ:finrank ℂ (L.map Rq)≤2:=by
  have od:L.map Rq≠ ⊤ :=by
   intro NA
   have :(single 0 1:Ft->ℂ)∈L.map Rq:=by rw[NA];trivial
   obtain⟨y,hy,O⟩:=B6.1 this;have e:=o Xs Y (-y) (L.neg_mem hy)
   have h0:p3 (Xs+ -y)=0:=by
    have r0:=congrFun O 0;have r1:=congrFun O 1;have r2:=congrFun O 2;simp[Rq]at r0 r1 r2;simp[p3,r0,r1,r2,s,Xk,Xl]
   exact W (e ▸ h0)
  have h3:=Q2 od;rw[M7]at h3;omega
 have aO:finrank ℂ L≤ finrank ℂ K+2:=by
  have h:=dx L Rq
  rw[show L ⊓ ker Rq=K from rfl]at h
  omega
 have KL:∀ z∈K,∀ c:ℂ,p2 (Li z+ c•Li Xs)=c^2*p3 Xs:=by
  intro z d c;have P:z∈L:=(A6.1 d).1;have l:Rq z=0:=(A6.1 d).2;have r:z (0,0)=0:=congrFun l 0;have j:z (0,1)=0:=congrFun l 1;have S:z (0,2)=0:=congrFun l 2
  have main:∀ c:ℂ,c≠0->p2 (Li z+ c•Li Xs)=c^2*p3 Xs:=by
   intro c hc;have e:=o (c•Xs) (C.smul_mem c Y) z P;rw[aaI]at e
   have e2:=Zz (c•Xs+ z) (by simp[Xk,j]) (by simp[Xl,S])
   rw[e]at e2
   have p:Li (c•Xs+ z)=Li z+ c•Li Xs:=by
    rw[E9,I4,add_comm]
   rw[p]at e2;simp[s,r]at e2
   have :c*(p2 (Li z+ c•Li Xs)- c^2*p3 Xs)=0:=by grind
   rcases A0.1 this with h | h
   .exact absurd h hc
   .grind
  by_cases hc:c=0
  .subst hc;rw[G2,B8,acY (Li z) (Li Xs),main 1 A7,
    main 2 G0,main 3 three_ne_zero]
   ring
  .exact main c hc
 set L2:=K.map Li with aV
 have aU:finrank ℂ L2≤1:=by
  apply F2 L2 (Li Xs)
  .intro M hM m p;obtain⟨m1,aI,M',aH,rfl⟩:=C5.1 hM;obtain⟨c,rfl⟩:=C6.1 aH;obtain⟨j,A,rfl⟩:=B6.1 aI;obtain⟨S,aL,rfl⟩:=B6.1 p;have e1:=KL j A c;have e2:=KL (j+ S) (K.add_mem A aL) c;rw[E9]at e2
   rw[show Li j+ c•Li Xs+ Li S=Li j+ Li S+ c•Li Xs by abel,e2,e1]
  .have h:=KL 0 K.zero_mem 1;rw[H5,C0,G1,one_pow,G8]at h;rw[h];exact W
 set Z:=K ⊓ ker Li with hZ
 have aP:finrank ℂ K=finrank ℂ L2+ finrank ℂ Z:=by
  have h:=dx K Li
  rw[show K ⊓ ker Li=Z from rfl,show K.map Li=L2 from rfl]at h
  omega
 have al:∀ z∈Z,z (0,0)=0/\z (0,1)=0/\z (0,2)=0/\z (1,1)=0/\
   z (1,2)=0/\z (2,1)=0/\z (2,2)=0:=by
  intro z d;have aM:=(A6.1 d).1;have l:Rq z=0:=(A6.1 aM).2;have t:Li z=0:=(A6.1 d).2;refine⟨congrFun l 0,congrFun l 1,congrFun l 2,congrFun t (0,0),
   congrFun t (0,1),congrFun t (1,0),congrFun t (1,1)⟩
 have E:∀ z∈Z,∀ X1∈C,X1 (0,1)=0->X1 (0,2)=0->
   z (1,0)*X1 (2,2)+ z (2,0)*X1 (1,2)=0/\
   z (1,0)*X1 (2,1)+ z (2,0)*X1 (1,1)=0:=by
  intro z d X1 RK h1 h2;obtain⟨Lu,Nu,G,H,RJ,J,e22⟩:=al z d;have P:z∈L:=(A6.1 (A6.1 d).1).1;have hf:∀ X∈C,z (1,0)*(X (0,1)*X (2,2)+ X (0,2)*X (2,1))+
    z (2,0)*(X (0,1)*X (1,2)+ X (0,2)*X (1,1))=0:=by
   intro X hX;have e:=o X hX z P;simp only[p3,A1,Lu,Nu,G,H,RJ,J,e22]at e;grind
  have fa:=hf (X1+ B) (C.add_mem RK ae);have fb:=hf (X1- B) (C.sub_mem RK ae);have fc:=hf (X1+ W2) (C.add_mem RK ag);have fd:=hf (X1- W2) (C.sub_mem RK ag);simp only[A1,G3,h1,h2,ay,az,aA,aB]at fa fb fc fd;constructor
  all_goals grind
 have hP:Xs (1,1)*Xs (2,2)+ Xs (1,2)*Xs (2,1)≠0:=by
  have :=Zz Xs Xk Xl;rw[s,G8]at this;rw[this]at W;simpa[p2,Li] using W
 have am:∀ z∈Z,z≠0->z (1,0)≠0/\z (2,0)≠0:=by
  intro z d QO;obtain⟨Lu,Nu,G,H,RJ,J,e22⟩:=al z d;obtain⟨Q,R⟩:=E z d Xs Y Xk Xl
  have aX:z (1,0)≠0\/z (2,0)≠0:=by
   by_contra hc;push Not at hc;apply QO;funext q;obtain⟨i,k⟩:=q;fin_cases i<;>fin_cases k
   .exact Lu
   .exact Nu
   .exact G
   .exact hc.1
   .exact H
   .exact RJ
   .exact hc.2
   .exact J
   .exact e22
  constructor
  .intro g
   have hb:z (2,0)≠0:=by tauto
   rw[g,F4,C0]at Q R;have Jo:Xs (1,2)=0:=(A0.1 Q).resolve_left hb;have aD:Xs (1,1)=0:=(A0.1 R).resolve_left hb;apply hP;rw[Jo,aD];ring
  .intro hb
   have g:z (1,0)≠0:=by tauto
   rw[hb,F4,B8]at Q R;have aF:Xs (2,2)=0:=(A0.1 Q).resolve_left g;have aE:Xs (2,1)=0:=(A0.1 R).resolve_left g;apply hP;rw[aF,aE];ring
 have au:1≤ finrank ℂ Z:=by omega
 have aC:Z≠ ⊥ :=by
  intro h;rw[h,F6]at au;omega
 obtain⟨r,F,QO⟩:=M0 _ |>.1 aC;obtain⟨g,hb⟩:=am r F QO
 have as:∀ m∈L2,m=0:=by
  intro m p;obtain⟨f,T,rfl⟩:=B6.1 p;have ax:f∈L:=(A6.1 T).1;have ai:Rq f=0:=(A6.1 T).2;obtain⟨Q,R⟩:=E r F f (aG ax) (congrFun ai 1) (congrFun ai 2);obtain⟨s1,s2⟩:=E r F Xs Y Xk Xl;have k0:=KL f T 0;have k1:=KL f T 1;simp only[G2,B8,G1,one_pow,G8,zero_pow G0,
   F4]at k0 k1
  have ao:=Zz Xs Xk Xl;rw[s,G8]at ao;rw[ao]at k1;simp only[p2,Li,LinearMap.coe_mk,AddHom.coe_mk,A1]at k0 k1;simp only[Fin.succ_zero_eq_one,Fin.succ_one_eq_two]at k0 k1;set a:=r (1,0);set b:=r (2,0);set u:=f (1,1);set v:=f (1,2);set w:=f (2,1);set x:=f (2,2);set U:=Xs (1,1);set V:=Xs (1,2);set W':=Xs (2,1);set X':=Xs (2,2)
  have e6:u*X'+ x*U+ v*W'+ w*V=0:=by grind
  have aK:b*(u*v)=0:=by grind
  have aJ:b*(u*V+ v*U)=0:=by
   grind
  have aj:U*V≠0:=by
   intro h;apply hP
   have :a*(U*X'+ V*W')= -2*b*(U*V):=by
    grind
   rw[h,C3]at this;exact (A0.1 this).resolve_left g
  have aT:u*v=0:=(A0.1 aK).resolve_left hb;have aS:u*V+ v*U=0:=(A0.1 aJ).resolve_left hb
  have hV:V≠0:=λh=> aj (by rw[h,C3])
  have hU:U≠0:=λh=> aj (by rw[h,F4])
  have hu:u=0:=by
   have :u^2*V=0:=by grind
   exact E6 (n:=2) (by norm_num) |>.1 ((A0.1 this).resolve_right hV)
  have hv:v=0:=by
   have :v^2*U=0:=by grind
   exact E6 (n:=2) (by norm_num) |>.1 ((A0.1 this).resolve_right hU)
  have hx:x=0:=by
   have :a*x=0:=by grind
   exact (A0.1 this).resolve_left g
  have hw:w=0:=by
   have :a*w=0:=by grind
   exact (A0.1 this).resolve_left g
  funext q;obtain⟨i,k⟩:=q;fin_cases i<;>fin_cases k
  .exact hu
  .exact hv
  .exact hw
  .exact hx
 have aR:finrank ℂ L2=0:=by
  have :L2= ⊥ :=by
   rw[I9];intro m p;rw[L5];exact as m p
  rw[this,F6]
 set N:(Ft× Ft->ℂ)→ₗ[ℂ] ℂ:=LinearMap.proj ((1:Ft),(0:Ft)) with aW
 have aN:finrank ℂ (Z.map N)≤1:=by
  have :=H4 (Z.map N);rwa[Module.finrank_self]at this
 have aY:=dx Z N
 have Ra:1≤ finrank ℂ ↥(Z ⊓ ker N):=by omega
 have aw:Z ⊓ ker N≠ ⊥ :=by
  intro h;rw[h,F6]at Ra;omega
 obtain⟨j,A,av⟩:=M0 _ |>.1 aw;have :=(am j (A6.1 A).1 av).1;exact this (A6.1 A).2
def MN (r:Ft):(Ft× Ft->ℂ)→ₗ[ℂ] (Ft->ℂ) where
 toFun X:=λk=> X (r,k)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def U8 (r:Ft) (X:Ft× Ft->ℂ) (h:∀ k,X (r,k)=0):p3 X=0:=by
 have a:=h 0;have b:=h 1;have c:=h 2;fin_cases r<;>simp only[p3]<;>simp_all
def agk (r j:Ft) (X:Ft× Ft->ℂ):
  p3 (X∘ Equiv.prodCongr (swap 0 r) (swap 0 j))=p3 X:=by
 fin_cases r<;>fin_cases j<;>
  simp +decide [p3,O0]<;>ring
def Vh (X:Ft× Ft->ℂ) (a:∀ k,X (0,k)=0)
  (b:∀ k,X (1,k)=0) (c:∀ k,X (2,k)=0):X=0:=by
 funext q;obtain⟨i,k⟩:=q;fin_cases i
 .exact a k
 .exact b k
 .exact c k
def F3 (L:Submodule ℂ (Ft× Ft->ℂ)) (X0:Ft× Ft->ℂ)
  (o:∀ X∈L ⊔ span ℂ {X0},∀ y∈L,p3 (X+ y)=p3 X) (od:p3 X0≠0):
  finrank ℂ L≤3:=by
 set C:=L ⊔ span ℂ {X0} with hC;have az:L≤ C:=K8;have N:X0∈C:=N6 (P0 X0)
 have hz:∀ y∈L,p3 y=0:=by
  intro y p;have :=o 0 C.zero_mem y p;rw[C0]at this;rw[this];simp[p3]
 have V:X0∉ L:=λh=> od (hz X0 h)
 have z:∀ X∈C,p3 X=0->X∈L:=by
  intro X b E;obtain⟨y,p,m,hm,rfl⟩:=C5.1 b;obtain⟨c,rfl⟩:=C6.1 hm;have e:=o (c•X0) (C.smul_mem c N) y p;rw[add_comm]at E;rw[E,aaI]at e
  have hc:c=0:=by
   rcases A0.1 e.symm with h | h
   .exact E6 (n:=3) (by norm_num) |>.1 h
   .exact absurd h od
  rw[hc,G2,B8];exact p
 have ay:finrank ℂ C=finrank ℂ L+1:=du L X0 V;by_contra U;push Not at U
 have F:∃ r,C.map (MN r)= ⊤ :=by
  by_contra g;push Not at g
  have S:∀ r,finrank ℂ L≤ finrank ℂ ↥(C ⊓ ker (MN r))+1:=by
   intro r;have h3:=Q2 (g r);rw[M7]at h3;have :=dx C (MN r);omega
  have f:∀ r,C ⊓ ker (MN r)≤ L:=by
   intro r X b;obtain⟨ap,as⟩:=A6.1 b;apply z X ap;apply U8 r;intro k;exact congrFun (C7.1 as) k
  set d:=C ⊓ ker (MN 0);set K1:=C ⊓ ker (MN 1);set a:=C ⊓ ker (MN 2);have u:∀ A B:Submodule ℂ (Ft× Ft->ℂ),A≤ L->B≤ L->
    finrank ℂ A+ finrank ℂ B≤ finrank ℂ ↥(A ⊓ B)+ finrank ℂ L:=by
   intro A B hA hB;have :=H3 A B;have :=E7 (sup_le hA hB);omega
  have Z:∀ X,X∈d->X∈K1->X∈a->X=0:=by
   intro X E R h2;apply Vh
   .intro k;exact congrFun (C7.1 (A6.1 E).2) k
   .intro k;exact congrFun (C7.1 (A6.1 R).2) k
   .intro k;exact congrFun (C7.1 (A6.1 h2).2) k
  have i1:(K1 ⊓ a) ⊓ (d ⊓ a)= ⊥ :=by
   rw[I9];intro X b;simp only[A6]at b;rw[L5];exact Z X b.2.1 b.1.1 b.1.2
  have i2:(K1 ⊓ a ⊔ d ⊓ a) ⊓ (d ⊓ K1)= ⊥ :=by
   rw[I9];intro X b;obtain⟨Q,W⟩:=A6.1 b;have ao:X∈a:=(sup_le inf_le_right inf_le_right:K1 ⊓ a ⊔ d ⊓ a≤ a) Q;rw[L5];exact Z X (A6.1 W).1 (A6.1 W).2 ao
  have d1:=H3 (K1 ⊓ a) (d ⊓ a);rw[i1,F6]at d1;have d2:=H3 (K1 ⊓ a ⊔ d ⊓ a) (d ⊓ K1);rw[i2,F6]at d2;have aw:K1 ⊓ a ⊔ d ⊓ a ⊔ d ⊓ K1≤ L:=
   sup_le (sup_le (inf_le_left.trans (f 1)) (inf_le_left.trans (f 0)))
    (inf_le_left.trans (f 0))
  have d3:=E7 aw;have aC:=u K1 a (f 1) (f 2);have aB:=u d a (f 0) (f 2);have aA:=u d K1 (f 0) (f 1);have k0:finrank ℂ L≤ finrank ℂ d+1:=S 0;have k1:finrank ℂ L≤ finrank ℂ K1+1:=S 1;have k2:finrank ℂ L≤ finrank ℂ a+1:=S 2;omega
 obtain⟨r,hr⟩:=F
 have abk:∀ v:Ft->ℂ,∃ X∈C,MN r X=v:=by
  intro v
  have :v∈C.map (MN r):=by rw[hr];trivial
  obtain⟨X,b,au⟩:=B6.1 this;exact⟨X,b,au⟩
 have G:∃ j,∃ X∈C,MN r X=single j 1/\X∉ L:=by
  by_contra g;push Not at g
  choose D O P using λj=> abk (single j 1)
  have al:∀ j,D j∈L:=λj=> g j (D j) (O j) (P j)
  set Y:=X0- ∑ j,X0 (r,j)•D j with hY
  have av:Y∈C:=C.sub_mem N (C.sum_mem λj _=> C.smul_mem _ (O j))
  have OU:MN r Y=0:=by
   rw[hY,map_sub,map_sum];simp only[I4,P];funext k;simp[MN,Finset.sum_apply,C1]
  have I2:Y∈L:=z Y av (U8 r Y (λk=> congrFun OU k))
  have ae: ∑ j,X0 (r,j)•D j∈L:=L.sum_mem λj _=> L.smul_mem _ (al j)
  apply V;have :=L.add_mem I2 ae;rwa[hY,sub_add_cancel]at this
 obtain⟨j,l,Vk,x,am⟩:=G
 have UE:p3 l≠0:=λh=> am (z l Vk h)
 set e:=Equiv.prodCongr (swap (0:Ft) r) (swap (0:Ft) j) with he;set T:(Ft× Ft->ℂ) ≃ₗ[ℂ] (Ft× Ft->ℂ):=LinearEquiv.funCongrLeft ℂ ℂ e with hT
 have ag:∀ X q,T X q=X (e q):=λX q=> rfl
 have w:∀ X,p3 (T X)=p3 X:=λX=> agk r j X
 have J:C.map T.toLinearMap=L.map T.toLinearMap ⊔ span ℂ {T X0}:=by
  rw[hC,Submodule.map_sup,O4,O6];rfl
 have Wk:∀ k:Ft,k≠0->swap (0:Ft) j k≠j:=by
  intro k hk h;apply hk;apply (swap (0:Ft) j).injective;rw[h,L9]
 obtain⟨V1,ai,K⟩:=abk (single (swap (0:Ft) j 1) 1);obtain⟨V2,aj,M⟩:=abk (single (swap (0:Ft) j 2) 1);have i:∀ (X:Ft× Ft->ℂ) (v:Ft->ℂ),MN r X=v-> ∀ k,X (r,k)=v k:=
  λX v h k=> congrFun h k
 have YX:∀ X k,T X (0,k)=X (r,swap (0:Ft) j k):=by
  intro X k;rw[ag];simp[he,L9]
 have t:∀ X∈C,T X∈L.map T.toLinearMap ⊔ span ℂ {T X0}:=by
  intro X b;rw[<- J];exact C4 b
 have ax:=afR (L.map T.toLinearMap) (T X0) ?_ (T l) (t l Vk) ?_ ?_ ?_ ?_
  (T V1) (t V1 ai) ?_ ?_ (T V2) (t V2 aj) ?_ ?_
 .rw[L6]at ax;omega
 .intro X b y p;rw[<- J]at b;obtain⟨s,Q,rfl⟩:=B6.1 b;obtain⟨H,U6,rfl⟩:=B6.1 p
  have R:T.toLinearMap s+ T.toLinearMap H=T (s+ H):=by simp
  rw[R];change p3 (T (s+ H))=p3 (T s);rw[w,w];exact o s Q H U6
 .rw[YX,i l _ x,L9];simp
 .rw[YX,i l _ x,C1,C9 (Wk 1 (by decide))]
 .rw[YX,i l _ x,C1,C9 (Wk 2 (by decide))]
 .rw[w];exact UE
 .rw[YX,i V1 _ K];simp
 .rw[YX,i V1 _ K,C1,C9];intro h;have :=(swap (0:Ft) j).injective h
  exact absurd this (by decide)
 .rw[YX,i V2 _ M,C1,C9];intro h;have :=(swap (0:Ft) j).injective h
  exact absurd this (by decide)
 .rw[YX,i V2 _ M];simp
def cr:Fq->Fq->Fin 2->Fq:=
 ![![![2,3],![2,3],![1,3],![1,2]],![![2,3],![2,3],![0,3],![0,2]],
  ![![1,3],![0,3],![0,1],![0,1]],![![1,2],![0,2],![0,1],![0,1]]]
def sl (c x:Fq) (s t:ℂ):Mt→ₗ[ℂ] (Ft× Ft->ℂ) where
 toFun Z q:= ![Z (q.1.succ,cr c x 0),Z (q.1.succ,cr c x 1),s*Z (q.1.succ,x)+ t*Z (q.1.succ,c)] q.2
 map_add' Z W:=by
  funext q;obtain⟨i,j⟩:=q;fin_cases j<;>simp<;>ring
 map_smul' a Z:=by
  funext q;obtain⟨i,j⟩:=q;fin_cases j<;>simp<;>ring
def aej (c x:Fq) (e:c≠x) (M:Mt) (k s t:ℂ) (a:M (0,cr c x 0)=0)
  (b:M (0,cr c x 1)=0) (d:M (0,c)=k*s) (f:M (0,x)=k*t):
  p4 M=k*p3 (sl c x s t M):=by
 fin_cases c<;>fin_cases x<;>simp at e<;>simp[cr]at a b d f<;>
  simp[p4,p3,sl,cr,a,b,d,f]<;>ring
lemma ZQ (A B:Ft× Ft->ℂ):
  p3 A=4*p3 (A+(1:ℂ)•B)-6*p3 (A+(2:ℂ)•B)+4*p3 (A+(3:ℂ)•B)- p3 (A+(4:ℂ)•B):=by
 simp only[p3,A1,A4,A5];ring
def B2L (L:Sq) (A:∀ t∈L,p4 (Bm+ t)=65) (M:finrank ℂ ↥(Ar L 0)=4)
  (c x:Fq) (o:c≠x) (s t:ℂ) (Y:Mt) (C:Y∈L ⊔ span ℂ {Bm}) (q:Y∉ L)
  (D:Y (0,cr c x 0)=0) (E:Y (0,cr c x 1)=0) (F:Y (0,c)=s) (J:Y (0,x)=t):
  ∃ Z∈Ar L 0,Z≠0/\sl c x s t Z=0:=by
 obtain⟨X,n,m,H,rfl⟩:=C5.1 C;obtain⟨l,rfl⟩:=C6.1 H
 have G:l≠0:=λh=> q (by rw[h,G2,B8];exact n)
 have a:∀ Z∈Ar L 0,∀ r:ℂ,r≠0->p3 (sl c x s t (Z+ r•(X+ l•Bm)))=65*l^4*r^3:=by
  intro Z b r i;obtain⟨u,d⟩:=(ei L 0 Z).1 b;have e1:=Ud L A (Z+ r•X) (L.add_mem u (L.smul_mem r n)) (r*l)
  have z:(r*l)•Bm+(Z+ r•X)=Z+ r•(X+ l•Bm):=by rw[smul_add,H0];abel
  rw[z]at e1;have g:=aej c x o (Z+ r•(X+ l•Bm)) r s t
   (by rw[A1,A4,d,D,smul_zero,B8])
   (by rw[A1,A4,d,E,smul_zero,B8])
   (by rw[A1,A4,d,F,A5,C0])
   (by rw[A1,A4,d,J,A5,C0])
  rw[e1]at g
  have :r*(p3 (sl c x s t (Z+ r•(X+ l•Bm)))-65*l^4*r^3)=0:=by
   grind
  rcases A0.1 this with h | h
  .exact absurd h i
  .grind
 have f:∀ Z∈Ar L 0,∀ r:ℂ,p3 (sl c x s t (Z+ r•(X+ l•Bm)))=65*l^4*r^3:=by
  intro Z b r;by_cases i:r=0
  .subst i;rw[G2,B8,ZQ (sl c x s t Z) (sl c x s t (X+ l•Bm))];simp only[<- I4,<- E9]
   rw[a Z b 1 A7,a Z b 2 (by norm_num),a Z b 3 (by norm_num),
    a Z b 4 (by norm_num)]
   ring
  .exact a Z b r i
 have N:=F3 ((Ar L 0).map (sl c x s t)) (sl c x s t (X+ l•Bm)) ?_ ?_
 .have K:=dx (Ar L 0) (sl c x s t)
  have aoP:0< finrank ℂ ↥(Ar L 0 ⊓ ker (sl c x s t)):=by omega
  obtain⟨Z,b,d⟩:=dk aoP;exact⟨Z,(A6.1 b).1,d,C7.1 (A6.1 b).2⟩
 .intro W B v hv;obtain⟨O,y,P,p,rfl⟩:=C5.1 B;obtain⟨r,rfl⟩:=C6.1 p;obtain⟨k,j,rfl⟩:=B6.1 y;obtain⟨w,Ra,rfl⟩:=B6.1 hv;have e1:=f k j r;have g:=f (k+ w) ((Ar L 0).add_mem j Ra) r;rw[E9,I4]at e1;rw[E9,E9,I4]at g;rw[e1,<- g];congr 1;abel
 .have e:=f 0 (Ar L 0).zero_mem 1;rw[C0,G1]at e;rw[e];simp[G]
section P5zS
open Submodule LinearMap
alias Q3:=mul_eq_zero
alias Q4:=Pi.single_apply
alias Q5:=smul_eq_mul
alias Q6:=Pi.smul_apply
alias R1:=Fin.sum_univ_three
alias R5:=Pi.add_apply
alias R8:=ite_true
alias R9:=ite_false
alias S0:=add_zero
alias S4:=map_add
alias S5:=map_smul
alias S6:=Fintype.sum_prod_type
alias S8:=Submodule.mem_map_of_mem
alias S9:=Fin.sum_univ_succ
alias T0:=Equiv.swap_apply_def
alias T4:=Submodule.smul_mem
alias T5:=inf_comm
alias T6:=mul_zero
alias T8:=mem_span_singleton
alias T9:=zero_smul
alias U1:=Submodule.mem_inf
alias U3:=Fin.forall_fin_succ
alias U4:=Fin.sum_univ_four
alias U5:=mem_sup
alias V0:=Submodule.mem_sup
alias V3:=finrank_bot
alias V6:=zero_mul
alias V7:=Submodule.add_mem
alias V8:=map_sub
alias V9:=inv_mul_cancel₀
alias W0:=Pi.zero_apply
alias W1:=Submodule.finrank_mono
alias W7:=mem_inf
alias W8:=Pi.sub_apply
alias X3:=Submodule.mem_span_singleton
alias X4:=sub_zero
alias X5:=not_or
alias X7:=mem_sup_left
alias X8:=mul_assoc
alias X9:=neg_ne_zero
alias Y0:=zero_add
alias Y2:=mem_sup_right
alias Y3:=LinearEquiv.finrank_eq
alias Y4:=Submodule.map_comp
alias Y5:=smul_ne_zero
alias Y6:=mem_span_singleton_self
alias Y7:=exists_mem_ne_zero_of_ne_bot
alias Y8:=eq_or_ne
alias Y9:=Submodule.mem_sup_left
alias Z2:=LinearMap.add_apply
alias Z6:=smul_zero
alias Z7:=Submodule.finrank_le
alias Z9:=lt_of_le_of_ne
alias Aa:=Pi.neg_apply
alias Ab:=finrank_span_singleton
alias Ac:=LinearMap.coe_mk
alias Ad:=AddHom.coe_mk
alias Ae:=smul_smul
alias Af:=Submodule.mem_map
alias Ag:=Fin.sum_univ_two
alias Ah:=dotProduct_comm
alias Ai:=Submodule.sub_mem
alias Aj:=sub_self
alias Ak:=mem_ker
alias Al:=LinearMap.comp_apply
alias Am:=LinearMap.mem_ker
alias An:=Submodule.mem_span_range_iff_exists_fun
alias Ao:=Finset.mul_sum
alias Ap:=Function.ne_iff
alias Aq:=neg_eq_of_add_eq_zero_right
alias As:=Module.finrank_fin_fun
alias At:=SetLike.exists_of_lt
alias Au:=Submodule.mem_top
alias Av:=Submodule.mem_bot
alias Aw:=one_smul
alias Ax:=Fintype.linearIndependent_iff
alias Ay:=Submodule.mem_span_singleton_self
alias Az:=mul_comm
alias Ba:=LinearMap.id_apply
alias Bb:=Submodule.finrank_sup_add_finrank_inf_eq
alias Bc:=Fintype.card_fin
alias Bd:=funext_iff
alias Be:=div_mul_eq_mul_div
alias Bf:=span_singleton_le_iff_mem
alias Bg:=Submodule.smul_mem_iff
alias Bh:=finrank_sup_add_finrank_inf_eq
alias Bi:=Module.finrank_self
alias Bj:=Submodule.finrank_eq_zero
alias Bk:=neg_eq_zero
alias Bl:=eq_top_of_finrank_eq
alias Bn:=sub_eq_zero
alias Bo:=add_comm
alias Bp:=Finset.sum_congr
alias Bq:=finrank_span_eq_card
alias Bs:=add_assoc
alias Bt:=Submodule.exists_mem_ne_zero_of_ne_bot
alias Bu:=dotProduct_add
alias Bv:=Matrix.mulVec_zero
alias Bw:=eq_div_iff
alias Bx:=mem_map_of_mem
alias By:=inf_le_right
alias Bz:=LinearMap.sub_apply
alias Ca:=LinearMap.smul_apply
alias Cb:=Submodule.map_sup
alias Cc:=Submodule.map_span
alias Cd:=Set.image_singleton
alias Ce:=le_sup_left
alias Cg:=RingHom.id_apply
alias Ch:=LinearMap.finrank_range_add_finrank_ker
alias Ci:=LinearMap.congr_fun
alias Cj:=eq_bot_iff
alias Ck:=Fin.eq_zero_or_eq_succ
alias Cl:=LinearIndependent.pair_iff
alias Cm:=Equiv.symm_swap
alias Co:=dotProduct_smul
alias Cp:=Finset.mem_univ
alias Cq:=div_mul_cancel₀
alias Cr:=inv_ne_zero
alias Ct:=add_dotProduct
alias Cu:=Subspace.finrank_add_finrank_dualAnnihilator_eq
alias Cv:=LinearMap.ker_eq_bot'
alias Cw:=Finset.sum_eq_single
alias Cx:=Set.range_subset_iff
alias Cy:=Submodule.subset_span
alias Cz:=Equiv.swap_apply_of_ne_of_ne
alias Da:=Equiv.symm_apply_apply
alias Db:=Matrix.mulVecLin_apply
alias Dc:=Submodule.finrank_lt_finrank_of_lt
alias Dd:=Matrix.cons_val_zero
alias De:=Matrix.cons_val_one
abbrev LV (A:Sq): Prop := ∀ t∈A,p4 (Bm+ t)=65
abbrev R0 (A:Sq): Prop := ∀ X∈A,∀ c,X (0,c)=0
abbrev Jf:=Fq->ℂ
lemma JH {A:Sq} {i:Fq} {Z:Mt} (h:Z∈Ar A i):af i Z=0:=
 funext λq=>((ei A i Z).1 h).2 q
def JK {P:Fq->Prop} (h:∀ m,P m):P 0/\P 1/\P 2/\P 3:=⟨h 0,h 1,h 2,h 3⟩
def Ju (i:Fq) (s:Jf):Mt:=λq=> if q.1=i then s q.2 else 0
def JM (i:Fq) (s:Jf) (Y:Mt):Mt:=λq=> if q.1=i then s q.2 else Y q
def JF (j k:Fq) (x y:Jf):Mt:=λq=> if q.1=j then x q.2 else if q.1=k then y q.2 else 0
def JN (j k:Fq) (x y:Jf) (Y:Mt):Mt:=
 λq=> if q.1=j then x q.2 else if q.1=k then y q.2 else Y q
lemma JS (i:Fq) (s:Jf) (Y:Mt) (t:ℂ):
 p4 (Y+ t•Ju i s)=p4 Y+ t*p4 (JM i s Y):=by
 fin_cases i<;>simp +decide only[p4,Ju,JM,A1,A4,
  A5,A9,A8,C3,B8]<;>grind
def JT (j k:Fq) (a:j≠k) (x y:Jf) (Y:Mt):
 p4 (Y+(2:ℂ)•JF j k x y)-2*p4 (Y+(1:ℂ)•JF j k x y)+ p4 Y=2*p4 (JN j k x y Y):=by
 fin_cases j<;>fin_cases k<;>simp +decide only[p4,JF,JN,A1,
  A4,A5,A9,A8,C3,B8]at a ⊢ <;>grind
def J0 (A:Sq) (a:LV A) (i:Fq) (s:Jf)
 (c:Ju i s∈A) (Y:Mt) (b:Y∈A ⊔ span ℂ {Bm}):p4 (JM i s Y)=0:=by
 have h:=Ko A a Y b _ c 1;rw[JS]at h;grind
def JO (A:Sq) (a:LV A) (j k:Fq) (d:j≠k)
 (x y:Jf) (b:JF j k x y∈A) (Y:Mt) (c:Y∈A ⊔ span ℂ {Bm}):
 p4 (JN j k x y Y)=0:=by
 have h:=JT j k d x y Y;rw[Ko A a Y c _ b,Ko A a Y c _ b]at h;grind
def J (u:Jf) (m:Fq):ℂ:=(if m=0 then 2*u 0 else 4*u m)-(u 0+2*u 1+2*u 2+2*u 3)
def Jj (u v w:Jf):Mt:=
 λq=> if q.1=0 then Bm q else if q.1=1 then u q.2 else if q.1=2 then v q.2 else w q.2
abbrev K4 (S U:Jf): Prop := ∀ m,4*S m*U m=(S 0+ S 1+ S 2+ S 3)*(U 0+ U 1+ U 2+ U 3)
abbrev Md (S:Jf): Prop :=S 0≠0\/S 1≠0\/S 2≠0\/S 3≠0
def Jw (U V W:Jf):ℂ:=4* ∑ m,U m*V m*W m-(∑ m,U m)*(∑ m,V m)*(∑ m,W m)
def sm (X:Jf):ℂ:=X 0+ X 1+ X 2+ X 3
def hn (r:Fq) (X:Jf):ℂ:=8*X 0+19*(X 1+ X 2+ X 3)-5*X r
def Jh (u v w:Jf):64*p4 (Jj u v w)=
 Jw (J u) (J v) (J w):=by
 simp +decide only[Jw,p4,Jj,J,Bm,C2,A9,A8];grind
abbrev D3 (i j k:Fq): Prop :=i≠0/\j≠0/\k≠0/\i≠j/\i≠k/\j≠k
def Jx:∀ i j k r:Fq,D3 i j k->r=0\/r=i\/r=j\/r=k:=by
 unfold D3;decide
def Jb (u v w:Jf):ℂ:=p4 (Jj u v w)
def Br (i:Fq):Fq->ℂ:=λc=> Bm (i,c)
lemma Jv (i:Fq):af i Bm=Br i:=rfl
lemma Ji (u v w:Jf):Jb u v w=Jb v u w:=by
 simp +decide only[Jb,Jj,p4,Bm,A9,A8];grind
lemma Jl (u v w:Jf):Jb u v w=Jb u w v:=by
 simp +decide only[Jb,Jj,p4,Bm,A9,A8];grind
lemma Jp (u a v w:Jf):Jb (u+ a) v w=Jb u v w+ Jb a v w:=by
 simp +decide only[Jb,Jj,p4,Bm,A1,A9,A8];grind
lemma Jt (c:ℂ) (u v w:Jf):Jb (c•u) v w=c*Jb u v w:=by
 simp +decide only[Jb,Jj,p4,Bm,A4,A5,A9,
  A8];grind
lemma Je (u v a w:Jf):Jb u (v+ a) w=Jb u v w+ Jb u a w:=by
 rw[Ji,Jp,Ji v,Ji a]
lemma Jg (u v w a:Jf):Jb u v (w+ a)=Jb u v w+ Jb u v a:=by
 rw[Jl,Je,Jl u w,Jl u a]
lemma O (c:ℂ) (u v w:Jf):Jb u (c•v) w=c*Jb u v w:=by
 rw[Ji,Jt,Ji]
lemma Jc (c:ℂ) (u v w:Jf):Jb u v (c•w)=c*Jb u v w:=by
 rw[Jl,O,Jl]
def JP (u v w:Jf):Jb u v w=Jb w v u:=by rw[Ji,Jl,Ji]
lemma Jm (u w:Jf):Jb u 0 w=0:=by
 have h:=O 0 u 0 w;rw[G2,F4]at h;exact h
lemma JA (u v:Jf):Jb u v 0=0:=by rw[Jl];exact Jm u v
lemma JU (i j k:Fq) (h:D3 i j k) (s:Jf) (Y:Mt) (e:∀ c,Y (0,c)=Bm (0,c)):
 p4 (JM i s Y)=Jb s (af j Y) (af k Y):=by
 have ⟨l,m,n,f,g,SU⟩:=h;have ⟨a,b,e2,d⟩:=JK e;simp only[Bm]at a b e2 d;fin_cases i<;>fin_cases j<;>fin_cases k<;>
  simp_all +decide [JM,Jb,Jj,p4,bu,Bm]<;>grind
lemma JV (i j k:Fq) (h:D3 i j k) (x y:Jf) (Y:Mt) (e:∀ c,Y (0,c)=Bm (0,c)):
 p4 (JN j k x y Y)=Jb (af i Y) x y:=by
 have ⟨l,m,n,f,g,SU⟩:=h;have ⟨a,b,e2,d⟩:=JK e;simp only[Bm]at a b e2 d;fin_cases i<;>fin_cases j<;>fin_cases k<;>
  simp_all +decide [JN,Jb,Jj,p4,bu,Bm]<;>grind
def Od (A:Sq) (Z:Mt) (a:Z∈A) (t:ℂ):Bm+ t•Z∈A ⊔ span ℂ {Bm}:=
 Submodule.add_mem _ (mem_sup_right (mem_span_singleton_self _))
  (mem_sup_left (A.smul_mem t a))
lemma Jy (j:Fq) (Z:Mt) (t:ℂ):af j (Bm+ t•Z)=Br j+ t•af j Z:=by
 funext c;simp[bu,Br]
def Ot (A:Sq) (d:LV A) (h0:R0 A)
 (i j k:Fq) (h:D3 i j k) (s:Jf) (e:Ju i s∈A) (Z:Mt) (b:Z∈A) (t:ℂ):
 Jb s (Br j+ t•af j Z) (Br k+ t•af k Z)=0:=by
 have a:=J0 A d i s e _ (Od A Z b t);rw[JU i j k h s _ (λc=> by simp[h0 Z b c]),Jy,Jy]at a
 exact a
def SL (A:Sq) (b:LV A) (a:R0 A)
 (i j k:Fq) (h:D3 i j k) (s:Jf) (d:Ju i s∈A) (Z:Mt) (c:Z∈A):
 Jb s (Br j) (Br k)=0/\Jb s (af j Z) (Br k)+ Jb s (Br j) (af k Z)=0/\
  Jb s (af j Z) (af k Z)=0:=by
 have e:=Ot A b a i j k h s d Z c 0;have f:=Ot A b a i j k h s d Z c 1;have g:=Ot A b a i j k h s d Z c (-1);simp only[Je,Jg,O,Jc]at e f g;refine⟨by grind,by grind,
  by grind⟩
def OI (A:Sq) (d:LV A) (h0:R0 A)
 (i j k:Fq) (h:D3 i j k) (x y:Jf) (e:JF j k x y∈A) (Z:Mt) (b:Z∈A) (t:ℂ):
 Jb (Br i+ t•af i Z) x y=0:=by
 have a:=JO A d j k h.2.2.2.2.2 x y e _ (Od A Z b t);rw[JV i j k h x y _ (λc=> by simp[h0 Z b c]),Jy]at a
 exact a
def PL (A:Sq) (b:LV A) (a:R0 A)
 (i j k:Fq) (h:D3 i j k) (x y:Jf) (c:JF j k x y∈A) (Z:Mt) (d:Z∈A):
 Jb (Br i) x y=0/\Jb (af i Z) x y=0:=by
 have e:=OI A b a i j k h x y c Z d 0;have f:=OI A b a i j k h x y c Z d 1;simp only[Jp,Jt]at e f;exact⟨by grind,by grind⟩
def J1 (i j k:Fq) (h:D3 i j k) (X:Mt) (b:∀ c,X (0,c)=0) (d:∀ c,X (i,c)=0):
 X=JF j k (af j X) (af k X):=by
 funext q;have ⟨r,c⟩:=q;have a:=h.2.2.2.2.2;rcases Jx i j k r h with rfl | rfl | rfl | rfl
 .simp[JF,b c,Ne.symm h.2.1,Ne.symm h.2.2.1]
 .simp[JF,d c,h.2.2.2.1,h.2.2.2.2.1]
 .simp[JF,bu]
 .simp[JF,bu,Ne.symm a]
def J2 (i j k:Fq) (h:D3 i j k) (X:Mt) (a:∀ c,X (0,c)=0) (b:∀ c,X (j,c)=0)
 (d:∀ c,X (k,c)=0):X=Ju i (af i X):=by
 funext q;have ⟨r,c⟩:=q;rcases Jx i j k r h with rfl | rfl | rfl | rfl
 .simp[Ju,a c,Ne.symm h.1]
 .simp[Ju,bu]
 .simp[Ju,b c,Ne.symm h.2.2.2.1]
 .simp[Ju,d c,Ne.symm h.2.2.2.2.1]
lemma Jq (i j:Fq) (a:i≠j) (x y:Jf):Ju i x+ Ju j y=JF i j x y:=by
 funext q;simp only[A1,Ju,JF];by_cases b:q.1=i
 .simp[b,a]
 · by_cases c:q.1=j
   .simp[b,c,Ne.symm a]
   .simp[b,c]
def dv (i:Fq):Fq->ℂ:=λc=>
 if i=1 then (if c=2 then 1 else if c=3 then -1 else 0)
 else if i=2 then (if c=1 then 1 else if c=3 then -1 else 0)
 else (if c=1 then 1 else if c=2 then -1 else 0)
def J3:∀ i j k:Fq,D3 i j k->Jb (Br k) (dv i) (dv j)=1\/Jb (Br k) (dv i) (dv j)= -1:=by
 intro i j k h;have ⟨d,e,f,a,b,c⟩:=h;fin_cases i<;>fin_cases j<;>fin_cases k<;>
  simp_all +decide [Jb,Jj,p4,dv,Br,Bm]<;>norm_num
def Ou (A:Sq) (d:LV A) (c:R0 A)
 (i j k:Fq) (h:D3 i j k) (a b:ℂ) (m:a≠0) (n:b≠0) (f:Ju i (a•dv i)∈A)
 (g:Ju j (b•dv j)∈A):False:=by
 have hX:JF i j (a•dv i) (b•dv j)∈A:=by
  rw[<- Jq i j h.2.2.2.1];exact A.add_mem f g
 have l:D3 k i j:=⟨h.2.2.1,h.1,h.2.1,Ne.symm h.2.2.2.2.1,Ne.symm h.2.2.2.2.2,h.2.2.2.1⟩;have e:=(PL A d c k i j l _ _ hX 0 A.zero_mem).1;rw[O,Jc]at e;rcases J3 i j k h with v | v<;>rw[v]at e<;>simp_all
abbrev Cn (A:Sq):Sq:=A ⊔ span ℂ {Bm}
def Ms (s:Jf):(Fq->ℂ)→ₗ[ℂ] Module.Dual ℂ (Fq->ℂ):=
 LinearMap.mk₂ ℂ (λu x=> Jb s x u) (λ_ _ _=> Jg _ _ _ _)
  (λc _ _=> by rw[A5];exact Jc c _ _ _) (λ_ _ _=> Je _ _ _ _)
  (λc _ _=> by rw[A5];exact O c _ _ _)
def Oa (s:Jf) (U V:Submodule ℂ (Fq->ℂ)) (h:∀ u∈U,∀ v∈V,Jb s v u=0):
 finrank ℂ U+ finrank ℂ V≤4+ finrank ℂ (ker (Ms s)):=by
 have a:U.map (Ms s)≤ V.dualAnnihilator:=by
  rintro _ ⟨u,b,rfl⟩;rw[mem_dualAnnihilator];exact h u b
 have c:=Subspace.finrank_add_finrank_dualAnnihilator_eq V;have d:=E7 a;have e:=dx U (Ms s);have g:=E7 (inf_le_right:U ⊓ ker (Ms s)≤ _);have f:finrank ℂ (Fq->ℂ)=4:=by simp
 grind
def OJ (ω:Mt→ₗ[ℂ] Mt→ₗ[ℂ] ℂ) (C R:Sq) (k:R≤ C) (Mq:∀ z∈C,ω z z=0)
 (D:∀ r∈R,∀ z∈C,ω r z=0)
 (hm:finrank ℂ C=finrank ℂ R+1\/finrank ℂ C=finrank ℂ R+3):
 ∃ e∈C,e∉ R/\ ∀ z∈C,ω e z=0:=by
 have p:∀ x∈C,∀ y∈C,ω x y= - ω y x:=by
  intro x F y G;have h:=Mq _ (C.add_mem F G);simp only[E9,LinearMap.add_apply,Mq x F,Mq y G]at h;grind
 have j:∀ P:Sq,P≤ C->finrank ℂ P< finrank ℂ C-> ∃ b∈C,b∉ P:=by
  intro P _ UY;by_contra A;push_neg at A;have :=E7 (show C≤ P from A);grind
 have sl:∀ b∈C,span ℂ {b}≤ C:=λb X=>(span_singleton_le_iff_mem _ _).2 X
 have ⟨a,f,n0⟩:=j R k (by grind)
 have f1:=du R a n0;have u:=sup_le k (sl a f);rcases hm with hm | hm
 · refine⟨a,f,n0,λz g=> ?_⟩
   rw[<- eq_of_le_of_finrank_eq u (by grind)]at g
   obtain⟨r,i,w,Y,rfl⟩:=mem_sup.1 g;obtain⟨c,rfl⟩:=mem_span_singleton.1 Y;rw[E9,I4,p a f r (k i),D r i a f,Mq a f];simp
 have ⟨d,m,J⟩:=j _ u (by grind)
 have f2:=du _ d J;have H:=sup_le u (sl d m);have ⟨b2,n,K⟩:=j _ H (by grind)
 have f3:=du _ b2 K;have W:=eq_of_le_of_finrank_eq (sup_le H (sl b2 n)) (by grind)
 have s:∀ e∈C,ω e a=0-> ω e d=0-> ω e b2=0-> ∀ z∈C,ω e z=0:=by
  intro e B T U V z g;rw[<- W]at g;obtain⟨y2,O,w2,E,rfl⟩:=mem_sup.1 g;obtain⟨t2,rfl⟩:=mem_span_singleton.1 E;obtain⟨y1,N,w1,S,rfl⟩:=mem_sup.1 O;obtain⟨t1,rfl⟩:=mem_span_singleton.1 S;obtain⟨r,i,w0,M,rfl⟩:=mem_sup.1 N;obtain⟨t0,rfl⟩:=mem_span_singleton.1 M;simp only[E9,I4,T,U,V,smul_zero,B8];rw[p e B r (k i),D r i e B,neg_zero]
 have a10:=p d m a f;have a20:=p b2 n a f;have Q:=p b2 n d m;by_cases g:ω a d=0/\ ω a b2=0/\ ω d b2=0
 .exact⟨a,f,n0,s a f (Mq a f) g.1 g.2.1⟩
 set e:= ω d b2•a- ω a b2•d+ ω a d•b2 with l;have t:e∈C:=C.add_mem (C.sub_mem (C.smul_mem _ f) (C.smul_mem _ m)) (C.smul_mem _ n);refine⟨e,t,λo=> g ?_,s e t ?_ ?_ ?_⟩
 · have m2:ω a d•b2∈R ⊔ span ℂ {a} ⊔ span ℂ {d}:=by
    have :ω a d•b2=e- ω d b2•a+ ω a b2•d:=by rw[l];abel
    rw[this];exact Submodule.add_mem _ (F8 _ (mem_sup_left (mem_sup_left o))
     (mem_sup_left (mem_sup_right (D6 _ _
      (mem_span_singleton_self _))))) (mem_sup_right (D6 _ _
      (mem_span_singleton_self _)))
   have v:ω a d=0:=by
    by_contra q;exact K ((Submodule.smul_mem_iff _ q).1 m2)
   have m1:ω a b2•d∈R ⊔ span ℂ {a}:=by
    have :ω a b2•d= ω d b2•a- e:=by rw[l,v,G2,B8];abel
    rw[this];exact F8 _ (mem_sup_right (D6 _ _
     (mem_span_singleton_self _))) (mem_sup_left o)
   have L:ω a b2=0:=by
    by_contra q;exact J ((Submodule.smul_mem_iff _ q).1 m1)
   have Z:ω d b2•a∈R:=by
    have :ω d b2•a=e:=by rw[l,v,L];simp
    rw[this];exact o
   have z3:ω d b2=0:=by
    by_contra q;exact n0 ((Submodule.smul_mem_iff _ q).1 Z)
   exact⟨v,L,z3⟩
 · simp only[l,E9,map_sub,I4,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,A5,Mq a f,a10,a20];grind
 · simp only[l,E9,map_sub,I4,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,A5,Mq d m,Q];grind
 · simp only[l,E9,map_sub,I4,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,A5,Mq b2 n];grind
def Om (s:Jf) (j k:Fq):Mt→ₗ[ℂ] Mt→ₗ[ℂ] ℂ:=
 LinearMap.mk₂ ℂ (λZ a=> Jb s (af j Z) (af k a))
  (λ_ _ _=> by rw[E9,Je]) (λc _ _=> by rw[I4,O,A5])
  (λ_ _ _=> by rw[E9,Jg]) (λc _ _=> by rw[I4,Jc,A5])
def Ov (A:Sq) (hA:LV A) (b:R0 A)
 (i j k:Fq) (h:D3 i j k) (s:Jf) (e:Ju i s∈A):∀ z∈Cn A,Om s j k z z=0:=by
 intro z g;obtain⟨a,d,w,f,rfl⟩:=mem_sup.1 g;obtain⟨c,rfl⟩:=mem_span_singleton.1 f;have ⟨e1,l,m⟩:=SL A hA b i j k h s e a d;show Jb s (af j (a+ c•Bm)) (af k (a+ c•Bm))=0;simp only[E9,I4,Jv,Je,Jg,O,Jc];grind
def Jd (A:Sq) (a:LV A) (b:finrank ℂ A=5) (j k:Fq):
 finrank ℂ (Ar A j)+ finrank ℂ (A.map (af j))=5/\
 finrank ℂ ((Ar A j).map (af k))+ finrank ℂ ↥(Ar A j ⊓ Ar A k)=finrank ℂ (Ar A j)/\
 finrank ℂ ((Cn A).map (af j))=finrank ℂ (A.map (af j))+1/\finrank ℂ (Cn A)=6/\
 finrank ℂ ↥(Ar A j ⊔ Ar A k)+ finrank ℂ ↥(Ar A j ⊓ Ar A k)=finrank ℂ (Ar A j)+ finrank ℂ (Ar A k):=by
 refine⟨?_,?_,?_,?_,finrank_sup_add_finrank_inf_eq _ _⟩
 .have :=dx A (af j);unfold Ar;grind
 · have e:Ar A j ⊓ Ar A k=Ar A j ⊓ ker (af k):=by
    unfold Ar;ext X;simp only[mem_inf];tauto
   rw[e];exact dx _ _
 · show finrank ℂ ((A ⊔ span ℂ {Bm}).map (af j))=_;rw[Submodule.map_sup,O4,O6];refine du _ _ (λhB=> ?_)
   have ⟨t,ht,d⟩:=mem_map.1 hB;exact WJ A a j t ht (λc=> by simpa[bu] using congrFun d c)
 .show finrank ℂ ↥(A ⊔ span ℂ {Bm})=6;rw[du A Bm (Pe A a),b]
def gl (A:Sq) (hA:LV A) (r:Fq) (Q:Mt) (f:Q∈Cn A)
 (d:af r Q=0):Q∈Ar A r:=by
 obtain⟨a,b,w,g,rfl⟩:=mem_sup.1 f;obtain⟨c,rfl⟩:=mem_span_singleton.1 g;have e:∀ q,a (r,q)+ c*Bm (r,q)=0:=λq=> by simpa[bu] using congrFun d q
 have hc:c=0:=by
  by_contra hc;refine WJ A hA r ((-c)⁻¹•a) (A.smul_mem _ b) (λq=> ?_)
  simp only[A4,A5];rw[show a (r,q)= -c*Bm (r,q) by grind,<- mul_assoc,G5 (neg_ne_zero.2 hc),G8]
 subst hc;exact (ei A r _).2 ⟨by simpa using b,λq=> by simpa using e q⟩
def OK (A:Sq) (m:LV A) (M:R0 A)
 (C:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (s:Jf) (Q:Ju i s∈A)
 (hm:finrank ℂ (A.map (af j))+ finrank ℂ (A.map (af k))+ finrank ℂ ↥(Ar A j ⊓ Ar A k)=5\/
  finrank ℂ (A.map (af j))+ finrank ℂ (A.map (af k))+ finrank ℂ ↥(Ar A j ⊓ Ar A k)=7):
 3≤ finrank ℂ ↥(Ar A j ⊓ Ar A k)+ finrank ℂ (ker (Ms s)):=by
 have ⟨W,X,Y,d4,d5⟩:=Jd A m C j k;obtain⟨U,d2',V,-,-⟩:=Jd A m C k j;have adT:Ar A k ⊓ Ar A j=Ar A j ⊓ Ar A k:=T5 _ _;rw[adT]at d2';have b:∀ r,Ar A r≤ Cn A:=λr=> le_trans (I6 A r) Ce
 have Mq:=Ov A m M i j k h s Q;have hs':∀ x∈Cn A,∀ y∈Cn A,Om s j k x y= - Om s j k y x:=by
  intro x G y H;have e:=Mq _ ((Cn A).add_mem G H);simp only[S4,Z2,Mq x G,Mq y H]at e;grind
 have K:∀ Z∈Ar A j,af j Z=0:=λZ hZ=> JH hZ
 have T:∀ Z∈Ar A k,af k Z=0:=λZ hZ=> JH hZ
 have g:∀ r∈Ar A j ⊔ Ar A k,∀ z∈Cn A,Om s j k r z=0:=by
  intro r g z a;obtain⟨S,N,J,B,rfl⟩:=U5.1 g;rw[S4,Z2,hs' J (b k B) z a];simp only[Om,LinearMap.mk₂_apply,K S N,T J B,Jm,JA,neg_zero,S0]
 have ⟨e,p,D,o⟩:=OJ (Om s j k) (Cn A) (Ar A j ⊔ Ar A k) (sup_le (b j) (b k)) Mq g
  (by grind)
 have akB:∀ z∈Cn A,Om s j k z e=0:=λz a=> by rw[hs' z a e p,o z a,neg_zero]
 by_cases F:af k e∈(Ar A j).map (af k)
 · by_cases E:af j e∈(Ar A k).map (af j)
   · exfalso;apply D;have ⟨Z1,UX,L⟩:=mem_map.1 E;have ⟨l,q,e2⟩:=mem_map.1 F;have P:e- Z1- l∈Ar A j:=gl A m j _ ((Cn A).sub_mem ((Cn A).sub_mem p (b k UX)) (b j q))
      (by rw[V8,V8,L,K l q,Aj,X4])
     have :e=(e- Z1- l)+ Z1+ l:=by abel
     rw[this];exact V7 _ (V7 _ (X7 P) (Y2 UX))
      (X7 q)
   · have f:=du _ _ E;have :=Oa s ((Cn A).map (af k)) ((Ar A k).map (af j) ⊔ span ℂ {af j e}) (by
      rintro _ ⟨z,a,rfl⟩ v hv;obtain⟨_,⟨Z,hZ,rfl⟩,w,t,rfl⟩:=U5.1 hv;obtain⟨c,rfl⟩:=T8.1 t;rw[Je,O];have d:=g Z (Y2 hZ) z a;have a2:=o z a;simp only[Om,LinearMap.mk₂_apply]at d a2;rw[d,a2];grind)
     grind
 · have f:=du _ _ F;have :=Oa s ((Ar A j).map (af k) ⊔ span ℂ {af k e}) ((Cn A).map (af j)) (by
    rintro u R _ ⟨z,a,rfl⟩;obtain⟨_,⟨Z,hZ,rfl⟩,w,t,rfl⟩:=U5.1 R;obtain⟨c,rfl⟩:=T8.1 t;rw[Jg,Jc];have d:=hs' z a Z (b j hZ);have n:=g Z (X7 hZ) z a;have a2:=akB z a;simp only[Om,LinearMap.mk₂_apply]at d n a2;rw[d,n,a2];grind)
   grind
def Jr {i j k:Fq} (h:D3 i j k):(i=1/\j=2/\k=3)\/(i=1/\j=3/\k=2)\/
 (i=2/\j=1/\k=3)\/(i=2/\j=3/\k=1)\/(i=3/\j=1/\k=2)\/(i=3/\j=2/\k=1):=by
 revert h;revert i j k;unfold D3;decide
lemma JQ (s u x:Jf):Ms s u x=Jb s x u:=rfl
def f4:∀ m:Fq,m=0\/m=1\/m=2\/m=3:=by decide
def xv (m:Fq):Fq->ℂ:=λc=> if c=0 then (if m=0 then 2 else -2) else if c=m then 1 else -1
def Jk (s u:Jf) (a:∀ x,Jb s x u=0):K4 (J s) (J u):=by
 intro m;have h:=Jh s (xv m) u;rw[show p4 (Jj s (xv m) u)=Jb s (xv m) u from rfl,a]at h;rcases f4 m with rfl | rfl | rfl | rfl<;>simp +decide only[Jw,xv,J,
  U4,R8,R9]at h ⊢ <;>grind
def Jz (l:Fq):(Fq->ℂ)→ₗ[ℂ] ℂ where
 toFun u:=J u l
 map_add' u v:=by simp only[J,R5];split_ifs<;>grind
 map_smul' c u:=by simp only[J,Q6,Q5,Cg];split_ifs<;>grind
def J4 (s:Jf) (l:Fq) (h:2≤ finrank ℂ (ker (Ms s))):
 ∃ u:Jf,(∀ x,Jb s x u=0)/\J u l=0/\u≠0:=by
 have c:=Ch (Jz l);have d:=Z7 (LinearMap.range (Jz l));have e:=Bh (ker (Ms s)) (ker (Jz l));have f:=Z7 (ker (Ms s) ⊔ ker (Jz l));simp only[As,Bi]at c d f;have ⟨u,a,b⟩:=Y7
  (p:=ker (Ms s) ⊓ ker (Jz l)) (by intro g;rw[g,V3]at e;grind)
 refine⟨u,λx=> ?_,Ak.1 a.2,b⟩
 have :=Ci (Ak.1 a.1) x;simpa[JQ] using this
def Ja (u:Jf) (b:u≠0):Md (J u):=by
 by_contra a;simp only[Md,X5,ne_eq,not_not]at a;have ⟨n0,d,e,f⟩:=a;simp +decide only[J,R8,R9]at n0 d e f;apply b;funext c;fin_cases c<;>simp
 .grind
 .grind
 .grind
 .grind
def Ow (S a b:Jf) (i j k:Fq) (h:D3 i j k) (d:hn i S=0) (p:a j=0) (q:b k=0)
 (ka:K4 S a) (c:K4 S b) (r:Md a) (s:Md b):S 0=0/\S i=0/\S j+ S k=0:=by
 have ⟨e,f,g,ka3⟩:=JK ka;have ⟨l,m,n,o⟩:=JK c;clear ka c;rcases Jr h with⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
  ⟨rfl,rfl,rfl⟩<;>simp only[hn]at d<;>refine⟨?_,?_,?_⟩<;>grind
def Ox (s:Jf) (i j k:Fq) (h:D3 i j k) (f:Jb s (Br j) (Br k)=0)
 (a:2≤ finrank ℂ (ker (Ms s))):∃ c:ℂ,s=c•dv i:=by
 have ⟨u,ku,b,d⟩:=J4 s j a;have ⟨v,kv,hv,e⟩:=J4 s k a;refine⟨s (if i=1 then 2 else 1),funext λc=> ?_⟩
 have r:=Ow _ _ _ i j k h ?_ b hv (Jk s u ku) (Jk s v kv) (Ja u d) (Ja v e)
 · clear ku kv b hv d e;rcases Jr h with⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩<;>simp +decide only[J,R8,R9]at r<;>fin_cases c<;>simp[dv]<;>grind
 · rcases Jr h with⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩<;>simp +decide only[hn,J,Jb,Jj,p4,Br,Bm,R8,R9]at f ⊢ <;>
    grind
def ON (i:Fq) (f:i≠0):finrank ℂ (ker (Ms (Br i)))=0:=by
 rw[Bj,Cv];intro u g;have e:∀ x,Jb (Br i) x u=0:=λx=> by
  have :=Ci g x;simpa[JQ] using this
 have a:=e (Pi.single 0 1);have b:=e (Pi.single 1 1);have e2:=e (Pi.single 2 1);have d:=e (Pi.single 3 1);funext c;fin_cases i<;>simp at f<;>
  simp +decide [Jb,Jj,p4,Br,Bm,Q4]at a b e2 d<;>
  fin_cases c<;>simp<;>grind
def Oe (A:Sq) (a:R0 A) (i j k:Fq) (h:D3 i j k)
 (X:Mt) (b:X∈A) (d:∀ c,X (i,c)=0) (e:∀ c,X (j,c)=0) (f:∀ c,X (k,c)=0):
 X=0:=by
 funext q;have ⟨r,c⟩:=q;rcases Jx i j k r h with rfl | rfl | rfl | rfl
 .exact a X b c
 .exact d c
 .exact e c
 .exact f c
def JL (A:Sq) (b:R0 A) (i j k:Fq) (h:D3 i j k) (T:Mt)
 (d:T∈Ar A j ⊓ Ar A k):Ju i (af i T)∈A/\(af i T=0->T=0):=by
 have ⟨a,c⟩:=W7.1 d;have e:=J2 i j k h T (b T (I6 A j a)) ((ei A j T).1 a).2 ((ei A k T).1 c).2;refine⟨by rw[<- e];exact I6 A j a,λhz=> ?_⟩
 rw[e,hz];funext q;simp[Ju]
def sw (A:Sq) (c:R0 A) (i j k:Fq) (h:D3 i j k):
 finrank ℂ ((Ar A j ⊓ Ar A k).map (af i))=finrank ℂ ↥(Ar A j ⊓ Ar A k):=by
 have e:=dx (Ar A j ⊓ Ar A k) (af i);have hb:(Ar A j ⊓ Ar A k) ⊓ ker (af i)= ⊥ :=by
  rw[Cj];intro Z d;have ⟨b,a⟩:=W7.1 d;exact (JL A c i j k h Z b).2 (Ak.1 a)
 rw[hb,V3]at e;grind
def pk (A:Sq) (i j:Fq) (h:finrank ℂ ↥(Ar A i ⊓ Ar A j)< finrank ℂ (Ar A i)):
 ∃ X∈Ar A i,af j X≠0:=by
 have ⟨X,a,b⟩:=At (Z9 (inf_le_left:Ar A i ⊓ Ar A j≤ Ar A i)
  (λe=> by rw[e]at h;grind))
 exact⟨X,a,λe=> b (W7.2 ⟨a,(ei A j X).2 ⟨I6 A i a,
  λq=> by simpa[bu] using congrFun e q⟩⟩)⟩
def Oy (A:Sq) (c:LV A) (b:R0 A)
 (i j k:Fq) (h:D3 i j k) (X:Mt) (a:X∈Ar A i) (Z:Mt) (d:Z∈A):
 Jb (Br i) (af j X) (af k X)=0/\Jb (af i Z) (af j X) (af k X)=0:=by
 have e:=J1 i j k h X (b X (I6 A i a)) ((ei A i X).1 a).2;exact PL A c b i j k h _ _ (by rw[<- e];exact I6 A i a) Z d
def J5 (A:Sq) (b:LV A) (a:R0 A)
 (n:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k):2≤ finrank ℂ (A.map (af i)):=by
 obtain⟨u,d2,-,-,-⟩:=Jd A b n i j;have e:D3 k i j:=⟨h.2.2.1,h.1,h.2.1,Ne.symm h.2.2.2.2.1,Ne.symm h.2.2.2.2.2,h.2.2.2.1⟩;have y:=sw A a k i j e;have l:Br j∉(Ar A i).map (af j):=λo=> by
  have ⟨t,r,q⟩:=mem_map.1 o;exact WJ A b j t (I6 A i r) (λc=> by simpa[bu,Br] using congrFun q c)
 have f:=du _ _ l;have hK:=Oa (Br i) ((Ar A i ⊓ Ar A j).map (af k)) ((Ar A i).map (af j) ⊔ span ℂ {Br j}) (by
  rintro _ ⟨T,p,rfl⟩ v hv;obtain⟨_,⟨X,m,rfl⟩,w,s,rfl⟩:=U5.1 hv;obtain⟨c,rfl⟩:=T8.1 s;have ⟨hTi,d⟩:=W7.1 p;have s1:=(SL A b a k i j e _ (JL A a k i j e T (W7.2 ⟨hTi,d⟩)).1 0 A.zero_mem).1;have z:=(Oy A b a i j k h X m 0 A.zero_mem).1;have p2:=(Oy A b a i j k h (X+ T) (V7 _ m hTi) 0 A.zero_mem).1;have g:af j T=0:=JH d;rw[S4,S4,g,S0,Jg]at p2;rw[Ji,Jl]at s1;rw[Je,O];grind)
 have x:=ON i h.1;grind
def Js (A:Sq) (hA:LV A) (a:R0 A)
 (g:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (f:finrank ℂ ↥(Ar A j ⊓ Ar A k)=1)
 (r:finrank ℂ (A.map (af j))+ finrank ℂ (A.map (af k))=4\/
  finrank ℂ (A.map (af j))+ finrank ℂ (A.map (af k))=6):
 ∃ c:ℂ,c≠0/\Ju i (c•dv i)∈A:=by
 have ⟨T,m,d⟩:=Y7 (p:=Ar A j ⊓ Ar A k)
  (by intro n;rw[n,V3]at f;grind)
 have ⟨b,q⟩:=JL A a i j k h T m;have l:=(SL A hA a i j k h _ b 0 A.zero_mem).1;have s:=OK A hA a g i j k h _ b (by grind)
 have ⟨c,e⟩:=Ox _ i j k h l (by grind)
 refine⟨c,λo=> d (q ?_),?_⟩
 .rw[e,o,T9]
 .rw[<- e];exact b
def JY (A:Sq) (d:LV A) (b:R0 A)
 (c:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k):
 finrank ℂ ↥(Ar A i ⊓ Ar A j)+ finrank ℂ ↥(Ar A i ⊓ Ar A k)≤ finrank ℂ (Ar A i)/\
 finrank ℂ (Ar A j)+ finrank ℂ (Ar A k)≤5+ finrank ℂ ↥(Ar A j ⊓ Ar A k):=by
 constructor
 · have e:=Bh (Ar A i ⊓ Ar A j) (Ar A i ⊓ Ar A k);have hb:(Ar A i ⊓ Ar A j) ⊓ (Ar A i ⊓ Ar A k)= ⊥ :=by
    rw[Cj];intro X a;simp only[W7]at a;exact Oe A b i j k h X (I6 A i a.1.1) ((ei A i X).1 a.1.1).2 ((ei A j X).1 a.1.2).2
     ((ei A k X).1 a.2.2).2
   rw[hb,V3,S0]at e;have :=W1 (sup_le inf_le_left inf_le_left:
    (Ar A i ⊓ Ar A j) ⊔ (Ar A i ⊓ Ar A k)≤ Ar A i)
   grind
 .obtain⟨-,-,-,-,f⟩:=Jd A d c j k;have :=W1 (sup_le (I6 A j) (I6 A k));grind
def Pm (a m c d:Fq): Prop :=a< m/\c< d/\a≠c/\a≠d/\m≠c/\m≠d
set_option synthInstance.maxSize 2048 in
def JD:∀ a m c d:Fq,Pm a m c d->(a=0/\m=1/\c=2/\d=3)\/(a=0/\m=2/\c=1/\d=3)\/
 (a=0/\m=3/\c=1/\d=2)\/(a=1/\m=2/\c=0/\d=3)\/(a=1/\m=3/\c=0/\d=2)\/
 (a=2/\m=3/\c=0/\d=1):=by
 unfold Pm;decide
def J6:∀ a m c d l:Fq,Pm a m c d->l=a\/l=m\/l=c\/l=d:=by unfold Pm;decide
def JZ:∀ a m:Fq,a< m-> ∃ c d,Pm a m c d:=by unfold Pm;decide
def JB {a m c d:Fq} (h:Pm a m c d) (f:Jf):sm f=f a+ f m+ f c+ f d:=by
 rcases JD _ _ _ _ h with⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
  ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩<;>simp only[sm]<;>grind
def OO (X b Y Y':Jf) (a m c d:Fq) (e:Pm a m c d) (q:X a=1) (r:X m=0)
 (B:b a=0) (M:b m=1) (P1:∀ n,4*X n*Y n=sm X*sm Y)
 (P2:∀ n,4*b n*Y' n=sm b*sm Y')
 (P3:∀ n,4*(X n*Y' n+ b n*Y n)=sm X*sm Y'+ sm b*sm Y)
 (F1:hn 1 X+ hn 2 Y=0) (F2:hn 1 b+ hn 2 Y'=0)
 (j:∀ g i:ℂ,g*Y a+ i*Y' a=0->g*Y m+ i*Y' m=0->g*Y c+ i*Y' c=0->
  g*Y d+ i*Y' d=0->g=0/\i=0):False:=by
 have w:=JB e X;have Z:=JB e b;have x:=JB e Y;have s4:=JB e Y';have N:=P1 a;have v:=P1 m;have Q:=P1 c;have T:=P1 d;have O:=P2 a;have W:=P2 m;have R:=P2 c;have U:=P2 d;have P:=P3 a;have m3:=P3 m;have S:=P3 c;have V:=P3 d;clear P1 P2 P3;by_cases k:Y' a=0
 · have l:Y a=0:=by grind
   have o:Y m=0:=by grind
   have z3:Y' m=0:=by grind
   have z4:Y c*Y' d=Y d*Y' c:=by grind
   have y:=j (Y' c) (-Y c) (by rw[l,k];grind) (by rw[o,z3];grind) (by grind) (by grind)
   have z:=j (Y' d) (-Y d) (by rw[l,k];grind) (by rw[o,z3];grind) (by grind) (by grind)
   have A:=j 1 0 (by rw[l];grind) (by rw[o];grind) (by rw[Bk.1 y.2];grind)
    (by rw[Bk.1 z.2];grind)
   exact one_ne_zero A.1
 · have s:X c*X d=0:=by grind
   have f:Y m=Y' a/\Y c= -Y' a*X d/\Y d= -Y' a*X c/\Y a=0:=
    ⟨by grind,by grind,by grind,by grind⟩
   have t:b c= -X d/\b d= -X c/\Y' c=Y' a*X c/\Y' d=Y' a*X d/\Y' m=0:=
    ⟨by grind,by grind,by grind,by grind,by grind⟩
   have u:(1+ X c+ X d)*(1- X c- X d)=0:=by
    have p:Y' a*((1+ X c+ X d)*(1- X c- X d))=0:=by
     rw[w,x,q,r,f.1,f.2.1,f.2.2.1,f.2.2.2]at v;grind
    exact (Q3.1 p).resolve_left k
   have ⟨C,D,E,F⟩:=f;have ⟨G,H,J,K,L⟩:=t;rcases Q3.1 s with h | h<;>rcases Q3.1 u with h' | h'<;>
    rcases JD _ _ _ _ e with⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
     ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩<;>simp only[hn]at F1 F2<;>grind
def Of:(Fq->ℂ)→ₗ[ℂ] (Fq->ℂ) where
 toFun u:=J u
 map_add' u v:=by funext l;simp only[J,R5];split_ifs<;>grind
 map_smul' c u:=by funext l;simp only[J,Q6,Q5,Cg];split_ifs<;>grind
def JW (u:Jf) (h:∀ l,J u l=0):u=0:=by
 by_contra a;rcases Ja u a with h1 | h1 | h1 | h1<;>exact h1 (h _)
def Og (K:Sq) (D:finrank ℂ K=2) (f:Mt→ₗ[ℂ] (Fq->ℂ))
 (q:∀ E∈K,f E=0->E=0):
 ∃ E∈K,∃ E'∈K,∃ a m c d,Pm a m c d/\f E a=1/\f E m=0/\f E' a=0/\f E' m=1:=by
 have w:∀ E∈K,E≠0-> ∃ l,f E l≠0:=λE e od=> by
  by_contra u;push_neg at u;exact od (q E e (funext u))
 have ⟨E0,g,B⟩:=Y7 (p:=K)
  (by intro j;rw[j,V3]at D;grind)
 have ⟨b,t⟩:=w E0 g B;have F:=dx K ((LinearMap.proj b).comp f);have v:=Z7 (K.map ((LinearMap.proj b).comp f));simp only[Bi]at v;have ⟨E1,C,r⟩:=Y7
  (p:=K ⊓ ker ((LinearMap.proj b).comp f)) (by intro j;rw[j,V3]at F;omega)
 have ⟨h1K,s⟩:=W7.1 C;have i:f E1 b=0:=by simpa using s
 have ⟨m0,n⟩:=w E1 h1K r;have od:b≠m0:=λh=> n (h ▸ i)
 have e:(f E0 b)⁻¹•(E0-(f E0 m0/f E1 m0)•E1)∈K:=K.smul_mem _ (K.sub_mem g (K.smul_mem _ h1K));have o:(f E1 m0)⁻¹•E1∈K:=K.smul_mem _ h1K;have x:f ((f E0 b)⁻¹•(E0-(f E0 m0/f E1 m0)•E1)) b=1:=by
  simp only[S5,V8,Q6,W8,Q5,i,T6,X4];exact V9 t
 have y:f ((f E0 b)⁻¹•(E0-(f E0 m0/f E1 m0)•E1)) m0=0:=by
  simp only[S5,V8,Q6,W8,Q5];field_simp;grind
 have z:f ((f E1 m0)⁻¹•E1) b=0:=by simp[i]
 have A:f ((f E1 m0)⁻¹•E1) m0=1:=by simp only[S5,Q6,Q5];exact V9 n
 rcases lt_or_gt_of_ne od with UY | UY
 .have ⟨c,d,k⟩:=JZ b m0 UY;exact⟨_,e,_,o,b,m0,c,d,k,x,y,z,A⟩
 .have ⟨c,d,k⟩:=JZ m0 b UY;exact⟨_,o,_,e,m0,b,c,d,k,A,z,y,x⟩
def Jn (A:Sq) (hA:LV A) (d:R0 A)
 (e:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (hp:finrank ℂ (A.map (af i))=3) (E:Mt)
 (f:E∈Ar A i) (w:Jf):Jb (af j E) w (af k E)=0:=by
 obtain⟨-,-,d3,-,-⟩:=Jd A hA e i j;have b:(Cn A).map (af i)= ⊤ :=Bl (by rw[d3,hp];simp)
 obtain⟨z,l,rfl⟩:=mem_map.1 (b ▸ Au:w∈(Cn A).map (af i));obtain⟨a,g,t,ht,rfl⟩:=U5.1 l;obtain⟨c,rfl⟩:=T8.1 ht;have ⟨m,p2⟩:=Oy A hA d i j k h E f a g;rw[Ji,S4,S5,Jv,Jp,Jt,p2,m];grind
def Ob (A:Sq) (c:LV A) (a:R0 A)
 (b:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (e:finrank ℂ (A.map (af i))=3) (X T:Mt)
 (d:X∈Ar A i) (f:T∈Ar A i) (g:af k T=0) (w:Jf):Jb (af j T) w (af k X)=0:=by
 have l:=Jn A c a b i j k h e X d w;have p2:=Jn A c a b i j k h e _ ((Ar A i).add_mem d f) w;simp only[S4,g,S0,Jp]at p2;grind
def F1 (A:Sq) (b:LV A) (f:R0 A) (i j k:Fq)
 (E:Mt) (a:E∈Ar A k) (h:D3 i j k:=by decide):
 hn i (J (af i E))+ hn j (J (af j E))=0:=by
 have d:=b E (I6 A k a);have e:=b (-E) (A.neg_mem (I6 A k a));have g:=f E (I6 A k a);have zk:=((ei A k E).1 a).2;have c:hn i (J (af i E))+ hn j (J (af j E))=(-2)*(p4 (Bm+ E)- p4 (Bm+ -E)):=by
  rcases Jr h with⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
   ⟨rfl,rfl,rfl⟩<;>simp +decide only[hn,J,p4,bu,Bm,R5,
   Aa,g,zk,R8,R9]<;>grind
 rw[c,d,e];grind
def OP (A:Sq) (k:LV A) (j:R0 A)
 (w:finrank ℂ A=5) (B:finrank ℂ (A.map (af 3))=3) (y:finrank ℂ (Ar A 3)=2):
 1≤ finrank ℂ ↥(Ar A 3 ⊓ Ar A 1)\/1≤ finrank ℂ ↥(Ar A 3 ⊓ Ar A 2):=by
 by_contra z;push_neg at z;have s:Ar A 3 ⊓ Ar A 1= ⊥ :=Bj.1 (by grind)
 have t:Ar A 3 ⊓ Ar A 2= ⊥ :=Bj.1 (by grind)
 have G:D3 3 1 2:=by decide
 have sg:∀ r,∀ E∈Ar A 3,(∀ l,J (af r E) l=0)->E∈Ar A 3 ⊓ Ar A r:=λr E b hz=> by
  have :=JW _ hz;exact W7.2 ⟨b,(ei A r E).2 ⟨I6 A 3 b,λc=> by simpa[bu] using congrFun this c⟩⟩
 have ⟨E,b,E',f,a,m,c,d,i,v1,o,p,q⟩:=Og (Ar A 3) y (Of.comp (af 1))
  (λE b hz=> by
   have :=sg 1 E b (λl=> congrFun hz l)
   rw[s]at this;exact (Av ℂ).1 this)
 have kE:∀ F∈Ar A 3,∀ n,4*J (af 1 F) n*J (af 2 F) n=
  sm (J (af 1 F))*sm (J (af 2 F)):=λF hF n=>
  Jk _ _ (λx=> Jn A k j w 3 1 2 G B F hF x) n
 have g:∀ r,J (af r (E+ E'))=J (af r E)+ J (af r E'):=λr=> by
  rw[S4];exact Of.map_add _ _
 refine OO (J (af 1 E)) (J (af 1 E')) (J (af 2 E)) (J (af 2 E')) a m c d i
  v1 o p q (kE E b) (kE E' f)
  (λn=> ?_) (F1 A k j 1 2 3 E b) (F1 A k j 1 2 3 E' f) (λα β H K L M=> ?_)
 .have h:=kE _ ((Ar A 3).add_mem b f) n;rw[g,g]at h;have u:=kE E b n;have v:=kE E' f n;simp only[sm,R5]at h u v ⊢;grind
 · have hz:α•E+ β•E'∈Ar A 3 ⊓ Ar A 2:=sg 2 _ ((Ar A 3).add_mem ((Ar A 3).smul_mem _ b)
    ((Ar A 3).smul_mem _ f)) (λl=> by
     have e:J (af 2 (α•E+ β•E')) l= α*J (af 2 E) l+ β*J (af 2 E') l:=by
      rw[S4,S5,S5];simp only[J,R5,Q6,Q5];split_ifs<;>grind
     rw[e];rcases J6 a m c d l i with rfl | rfl | rfl | rfl<;>assumption)
   rw[t,Av]at hz;have e:∀ l,J (af 1 (α•E+ β•E')) l= α*J (af 1 E) l+ β*J (af 1 E') l:=λl=> by
    rw[S4,S5,S5];simp only[J,R5,Q6,Q5];split_ifs<;>grind
   have C:α*J (af 1 E) a+ β*J (af 1 E') a=0:=by rw[<- e,hz];simp[J]
   have D:α*J (af 1 E) m+ β*J (af 1 E') m=0:=by rw[<- e,hz];simp[J]
   change J (af 1 E) a=1 at v1;change J (af 1 E) m=0 at o;change J (af 1 E') a=0 at p;change J (af 1 E') m=1 at q;rw[v1,p]at C;rw[o,q]at D;exact⟨by grind,by grind⟩
lemma JG (A:Sq) (a:Equiv.Perm Fq) (r:Fq):
 Ar (A.map (gp a)) r=(Ar A (a.symm r)).map (gp a):=by
 ext X;simp only[ei,mem_map];constructor
 .rintro⟨⟨Y,b,rfl⟩,hz⟩;exact⟨Y,⟨b,λc=> by simpa[my] using hz (a c)⟩,rfl⟩
 .rintro⟨Y,⟨b,hz⟩,rfl⟩;exact⟨⟨Y,b,rfl⟩,λc=> by simp[my,hz]⟩
lemma JC (A:Sq) (a:Equiv.Perm Fq) (r b:Fq):
 finrank ℂ ↥(Ar (A.map (gp a)) r ⊓ Ar (A.map (gp a)) b)=
  finrank ℂ ↥(Ar A (a.symm r) ⊓ Ar A (a.symm b)):=by
 rw[JG,JG,<- Submodule.map_inf (gp a) (O5 a)];exact (Y3 (equivMapOfInjective _ (O5 a) _)).symm
def JI (A:Sq) (e:LV A) (h0:R0 A)
 (d:finrank ℂ A=5) (a:Equiv.Perm Fq) (b:a 0=0):
 (∀ t∈A.map (gp a),p4 (Bm+ t)=65)/\(∀ X∈A.map (gp a),∀ c,X (0,c)=0)/\
  finrank ℂ (A.map (gp a))=5:=by
 refine⟨LY A e a,?_,by rw[o6];exact d⟩
 rintro _ ⟨Y,f,rfl⟩ c;have :a.symm 0=0:=by rw[Equiv.symm_apply_eq];exact b.symm
 rw[my,this];exact h0 Y f _
def JR (i j k:Fq) (h:D3 i j k):∃ a:Equiv.Perm (Fq),a 0=0/\a.symm 3=i/\
 a.symm 1=j/\a.symm 2=k:=by
 rcases Jr h with⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
  ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
 .exact⟨Equiv.swap 1 2*Equiv.swap 1 3,by decide⟩
 .exact⟨Equiv.swap 1 3,by decide⟩
 .exact⟨Equiv.swap 2 3,by decide⟩
 .exact⟨Equiv.swap 1 3*Equiv.swap 1 2,by decide⟩
 .exact⟨1,by decide⟩
 .exact⟨Equiv.swap 1 2,by decide⟩
def Pa (A:Sq) (l:LV A) (h0:R0 A)
 (h5:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (n:finrank ℂ (A.map (af i))=3)
 (m:finrank ℂ (Ar A i)=2):1≤ finrank ℂ ↥(Ar A i ⊓ Ar A j)\/1≤ finrank ℂ ↥(Ar A i ⊓ Ar A k):=by
 obtain⟨c,b,a,g,e2⟩:=JR i j k h;have ⟨e,d,f⟩:=JI A l h0 h5 c b;have r:=OP _ e d f (by rw[KW,a];exact n) (by
  rw[JG,<- m,a];exact (Y3 (equivMapOfInjective _ (O5 c) _)).symm)
 rw[JC,JC,a,g,e2]at r;exact r
def Oh (A:Sq) (a:LV A) (b:R0 A)
 (c:finrank ℂ A=5) (v:ℕ) (hv:v=2\/v=3) (r:finrank ℂ (A.map (af 1))=v)
 (p2:finrank ℂ (A.map (af 2))=v) (p3:finrank ℂ (A.map (af 3))=v):False:=by
 have d:D3 1 2 3:=by decide
 have f:D3 2 1 3:=by decide
 have e:D3 3 1 2:=by decide
 have ⟨u,w⟩:=JY A a b c 1 2 3 d;have ⟨p,z⟩:=JY A a b c 2 1 3 f;have ⟨q,B⟩:=JY A a b c 3 1 2 e;obtain⟨C,-⟩:=Jd A a c 1 2;obtain⟨D,-⟩:=Jd A a c 2 1;obtain⟨E,-⟩:=Jd A a c 3 1;rw[T5 (Ar A 2) (Ar A 1)]at p;rw[T5 (Ar A 3) (Ar A 1),T5 (Ar A 3) (Ar A 2)]at q;have o:(finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)=1/\finrank ℂ ↥(Ar A 1 ⊓ Ar A 3)=1)\/
  (finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)=1/\finrank ℂ ↥(Ar A 1 ⊓ Ar A 2)=1)\/
  (finrank ℂ ↥(Ar A 1 ⊓ Ar A 3)=1/\finrank ℂ ↥(Ar A 1 ⊓ Ar A 2)=1):=by
  rcases hv with rfl | rfl
  .grind
  have F:=Pa A a b c 1 2 3 d r (by grind)
  have s:=Pa A a b c 2 1 3 f p2 (by grind)
  have t:=Pa A a b c 3 1 2 e p3 (by grind)
  rw[T5 (Ar A 2) (Ar A 1)]at s;rw[T5 (Ar A 3) (Ar A 1),T5 (Ar A 3) (Ar A 2)]at t;grind
 rcases o with⟨x,y⟩ | ⟨x,y⟩ | ⟨x,y⟩
 · have ⟨g,l,j⟩:=Js A a b c 1 2 3 d x (by grind)
   have ⟨h,m,k⟩:=Js A a b c 2 1 3 f y (by grind)
   exact Ou A a b 1 2 3 d g h l m j k
 · have ⟨g,l,j⟩:=Js A a b c 1 2 3 d x (by grind)
   have ⟨i,n,m3⟩:=Js A a b c 3 1 2 e y (by grind)
   exact Ou A a b 3 1 2 e i g n l m3 j
 · have ⟨h,m,k⟩:=Js A a b c 2 1 3 f x (by grind)
   have ⟨i,n,m3⟩:=Js A a b c 3 1 2 e y (by grind)
   exact Ou A a b 3 2 1 (by decide) i h n m m3 k
def JE (a b c:ℕ): Prop := ∀ A:Sq,(∀ t∈A,p4 (Bm+ t)=65)->(∀ X∈A,∀ c,X (0,c)=0)->
 finrank ℂ A=5->finrank ℂ (A.map (af 1))=a->finrank ℂ (A.map (af 2))=b->
 finrank ℂ (A.map (af 3))=c->False
def Os (A:Sq) (hA:LV A) (h0:R0 A)
 (h5:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (a b c:ℕ) (H:JE a b c)
 (l:finrank ℂ (A.map (af j))=a) (m:finrank ℂ (A.map (af k))=b)
 (n:finrank ℂ (A.map (af i))=c):False:=by
 obtain⟨o,hσ,e3,f,g⟩:=JR i j k h;have ⟨d,Kj,e⟩:=JI A hA h0 h5 o hσ;exact H _ d Kj e (by rw[KW,f,l]) (by rw[KW,g,m]) (by rw[KW,e3,n])
def Oz (d:JE 2 2 3) (e:JE 2 3 3) (A:Sq) (a:LV A)
 (b:R0 A) (c:finrank ℂ A=5):False:=by
 have f:D3 1 2 3:=by decide
 have g:D3 2 1 3:=by decide
 have h:D3 3 1 2:=by decide
 have i:=J5 A a b c 1 2 3 f;have j:=J5 A a b c 2 1 3 g;have k:=J5 A a b c 3 1 2 h;have l:=QV A a 1;have m:=QV A a 2;have n:=QV A a 3;rcases (by grind :finrank ℂ (A.map (af 1))=2\/finrank ℂ (A.map (af 1))=3) with x | x<;>
 rcases (by grind :finrank ℂ (A.map (af 2))=2\/finrank ℂ (A.map (af 2))=3) with y | y<;>
 rcases (by grind :finrank ℂ (A.map (af 3))=2\/finrank ℂ (A.map (af 3))=3) with z | z
 .exact Oh A a b c 2 (by grind) x y z
 .exact d A a b c x y z
 .exact Os A a b c 2 1 3 g 2 2 3 d x z y
 .exact e A a b c x y z
 .exact Os A a b c 1 2 3 f 2 2 3 d y z x
 .exact Os A a b c 3 2 1 (by decide) 2 3 3 e y x z
 .exact Os A a b c 2 3 1 (by decide) 2 3 3 e z x y
 .exact Oh A a b c 3 (by grind) x y z
def dN (S:Jf):ℂ:=4*(S 0*S 1*S 2*S 3)-
 (S 0+ S 1+ S 2+ S 3)*(S 0*S 1*S 2+ S 0*S 1*S 3+ S 0*S 2*S 3+ S 1*S 2*S 3)
def OA (S U:Jf) (a:K4 S U)
 (b:Md U):dN S=0:=by
 have ⟨c,d,e,f⟩:=JK a;clear a;simp only[dN];grind
def OQ (P Q w:Jf) (i:P 0=0) (j:Q 3=0) (n:19*P 1+19*P 2+14*P 3=0)
 (o:8*Q 0+19*Q 1+19*Q 2=0) (c:dN P=0) (d:dN Q=0)
 (g:∀ m,w m=(Q 0+ Q 1- Q 2)*P m+(P 1- P 2+ P 3)*Q m) (h:dN w=0)
 (p:Md P) (q:Md Q):P 3=0/\Q 0=0:=by
 have ⟨k,r,s,l⟩:=JK g;clear g;simp only[dN,i,j]at c d h k l;have a:(P 1+ P 2+ P 3)*P 1*P 2*P 3=0:=by grind
 have b:(Q 0+ Q 1+ Q 2)*Q 0*Q 1*Q 2=0:=by grind
 clear c d;simp only[Q3]at a b;rcases a with ((e | e) | e) | e<;>rcases b with ((f | f) | f) | f<;>grind
def OR (P R w:Jf) (f:P 0=0) (h:P 3=0) (n:19*P 1+19*P 2+14*P 3=0)
 (p:Md P) (g:R 1=0)
 (o:8*R 0+19*R 2+14*R 3=0) (b:dN R=0)
 (c:∀ m,w m=(R 0+ R 2- R 3)*P m+(P 1- P 2+ P 3)*R m) (d:dN w=0)
 (q:Md R):False:=by
 have ⟨i,j,k,l⟩:=JK c;clear c;simp only[dN,f,h,g]at b d i j k l;have a:(R 0+ R 2+ R 3)*R 0*R 2*R 3=0:=by grind
 clear b;simp only[Q3]at a;rcases a with ((e | e) | e) | e<;>grind
def kv (W:Submodule ℂ (Fq->ℂ)) (l:Fq) (h:2≤ finrank ℂ W):∃ u∈W,J u l=0/\u≠0:=by
 have c:=Ch (Jz l);have d:=Bh W (ker (Jz l));have e:=Z7 (W ⊔ ker (Jz l));have f:=Z7 (LinearMap.range (Jz l));simp only[As,Bi]at c e f;have ⟨u,a,b⟩:=Y7 (p:=W ⊓ ker (Jz l))
  (by intro g;rw[g,V3]at d;grind)
 exact⟨u,a.1,Ak.1 a.2,b⟩
def JJ (a b:ℂ) (u v:Jf) (m:Fq):J (a•u+ b•v) m=a*J u m+ b*J v m:=by
 simp only[J,R5,Q6,Q5];split_ifs<;>grind
def OS (A:Sq) (j:LV A) (c:R0 A)
 (w:finrank ℂ A=5) (l:finrank ℂ ↥(Ar A 1 ⊓ Ar A 2)=2)
 (K:finrank ℂ (A.map (af 1))+ finrank ℂ (A.map (af 2))=5):False:=by
 have d:D3 3 1 2:=by decide
 have a:∀ u∈(Ar A 1 ⊓ Ar A 2).map (af 3),dN (J u)=0/\
  8*J u 0+19*J u 1+19*J u 2+14*J u 3=0:=by
  rintro _ ⟨T,y,rfl⟩;have k:=(JL A c 3 1 2 d T y).1;have B:=OK A j c w 3 1 2 d _ k (by grind)
  have ⟨v,hv,q⟩:=Y7 (p:=ker (Ms (af 3 T)))
   (by intro z;rw[z,V3]at B;grind)
  have kv':∀ x,Jb (af 3 T) x v=0:=λx=> by
   have :=Ci (Ak.1 hv) x;simpa[JQ] using this
  have hH:=(SL A j c 3 1 2 d _ k 0 A.zero_mem).1;refine⟨OA _ _ (Jk _ _ kv') (Ja v q),?_⟩;simp +decide only[J,Jb,Jj,p4,Br,Bm,R8,R9]at hH ⊢;grind
 have h:=(sw A c 3 1 2 d).trans l;have ⟨b,g,o,n⟩:=kv _ 0 h.ge;have ⟨i,e,E,C⟩:=kv _ 3 h.ge;have ⟨u3,f,z3,D⟩:=kv _ 1 h.ge;have ⟨s,F⟩:=a b g;have ⟨t,G⟩:=a i e;have ⟨f3,H⟩:=a u3 f;obtain⟨r,-⟩:=OQ (J b) (J i) _ o E (by grind)
  (by grind) s t (λm=> JJ _ _ _ _ m)
  (a _ (V7 _ (T4 _ _ g) (T4 _ _ e))).1
  (Ja b n) (Ja i C)
 exact OR (J b) (J u3) _ o r (by grind) (Ja b n) z3
  (by grind) f3 (λm=> JJ _ _ _ _ m)
  (a _ (V7 _ (T4 _ _ g) (T4 _ _ f))).1 (Ja u3 D)
def NL (A:Sq) (l:LV A) (h0:R0 A)
 (h5:finrank ℂ A=5) (i j k:Fq) (h:D3 i j k) (d:finrank ℂ ↥(Ar A j ⊓ Ar A k)=2)
 (m:finrank ℂ (A.map (af j))+ finrank ℂ (A.map (af k))=5):False:=by
 obtain⟨n,a,o,b,c⟩:=JR i j k h;have ⟨f,e,g⟩:=JI A l h0 h5 n a;exact OS _ f e g (by rw[JC,b,c];exact d) (by rw[KW,KW,b,c];exact m)
def JX (s:ℕ): Prop := ∀ A:Sq,(∀ t∈A,p4 (Bm+ t)=65)->(∀ X∈A,∀ c,X (0,c)=0)->
 finrank ℂ A=5->finrank ℂ (A.map (af 1))=2->finrank ℂ (A.map (af 2))=3->finrank ℂ (A.map (af 3))=3->
 finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)=s->finrank ℂ ↥(Ar A 1 ⊓ Ar A 3)≤1->finrank ℂ ↥(Ar A 1 ⊓ Ar A 2)≤1->False
def J7 (s:ℕ): Prop := ∀ A:Sq,(∀ t∈A,p4 (Bm+ t)=65)->(∀ X∈A,∀ c,X (0,c)=0)->
 finrank ℂ A=5->finrank ℂ (A.map (af 1))=2->finrank ℂ (A.map (af 2))=2->finrank ℂ (A.map (af 3))=3->
 finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)=1->finrank ℂ ↥(Ar A 1 ⊓ Ar A 3)≤1->finrank ℂ ↥(Ar A 1 ⊓ Ar A 2)=s->False
def J8 (H:∀ s,s≤2->JX s):JE 2 3 3:=by
 intro A b c a x y z;have d:D3 2 1 3:=by decide
 have tc:D3 3 1 2:=by decide
 obtain⟨h,-⟩:=Jd A b a 2 1;obtain⟨i,-⟩:=Jd A b a 3 1;obtain⟨f,-⟩:=JY A b c a 2 1 3 d;obtain⟨g,-⟩:=JY A b c a 3 1 2 tc;rw[T5 (Ar A 2) (Ar A 1)]at f;rw[T5 (Ar A 3) (Ar A 1),T5 (Ar A 3) (Ar A 2)]at g;have j:finrank ℂ ↥(Ar A 1 ⊓ Ar A 3)≠2:=λe=> NL A b c a 2 1 3 d e (by grind)
 have k:finrank ℂ ↥(Ar A 1 ⊓ Ar A 2)≠2:=λe=> NL A b c a 3 1 2 tc e (by grind)
 exact H _ (by grind) A b c a x y z rfl (by grind) (by grind)
def J9 (H:∀ s,1≤ s->s≤2->J7 s):JE 2 2 3:=by
 have Kr:D3 1 2 3:=by decide
 have i:D3 3 1 2:=by decide
 have d:∀ A:Sq,(∀ t∈A,p4 (Bm+ t)=65)->(∀ X∈A,∀ c,X (0,c)=0)->
  finrank ℂ A=5->finrank ℂ (A.map (af 1))=2->finrank ℂ (A.map (af 2))=2->
  finrank ℂ (A.map (af 3))=3->1≤ finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)->False:=by
  intro A b h0 a x y z h;obtain⟨u,-⟩:=Jd A b a 1 2;obtain⟨v,-⟩:=Jd A b a 2 1;obtain⟨p,-⟩:=Jd A b a 3 1;have ⟨n,b3⟩:=JY A b h0 a 3 1 2 i;obtain⟨r,-⟩:=JY A b h0 a 1 2 3 Kr;obtain⟨m,-⟩:=JY A b h0 a 2 1 3 (by decide)
  rw[T5 (Ar A 3) (Ar A 1),T5 (Ar A 3) (Ar A 2)]at n;rw[T5 (Ar A 2) (Ar A 1)]at m;have w:finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)≠2:=λe=> NL A b h0 a 1 2 3 Kr e (by grind)
  exact H _ (by grind) (by grind) A b h0 a x y z (by grind) (by grind) rfl
 intro A b h0 a x y z;by_cases h:1≤ finrank ℂ ↥(Ar A 2 ⊓ Ar A 3)
 .exact d A b h0 a x y z h
 obtain⟨p,-⟩:=Jd A b a 3 1;have q:=Pa A b h0 a 3 1 2 i z (by grind)
 have o:(Equiv.swap (1:Fq) 2).symm 1=2:=by decide
 have f:(Equiv.swap (1:Fq) 2).symm 2=1:=by decide
 have g:(Equiv.swap (1:Fq) 2).symm 3=3:=by decide
 have ⟨k,j,l⟩:=JI A b h0 a (Equiv.swap 1 2) (by decide)
 refine d _ k j l (by rw[KW,o,y]) (by rw[KW,f,x]) (by rw[KW,g,z]) ?_
 rw[JC,f,g,T5 (Ar A 3) (Ar A 1)]at *
 rw[T5 (Ar A 3) (Ar A 2)]at q;grind
def Oi (A:Sq) (c:LV A) (d:R0 A)
 (X Y:Mt) (e:X∈Ar A 2) (f:Y∈Ar A 3):
 Jb (Br 1) (af 2 Y) (af 3 X)+ Jb (af 1 Y) (Br 2) (af 3 X)+ Jb (af 1 X) (af 2 Y) (Br 3)=0:=by
 have a:=I6 A 2 e;have b:=I6 A 3 f;have h:=c _ (A.add_mem a b);have i:=c _ (A.sub_mem a b);have j:=c _ (A.sub_mem b a);have k:=c _ (A.neg_mem (A.add_mem a b));have x0:=d X a;have l:=d Y b;have x2:=((ei A 2 X).1 e).2;have m:=((ei A 3 Y).1 f).2;have g:4*(Jb (Br 1) (af 2 Y) (af 3 X)+ Jb (af 1 Y) (Br 2) (af 3 X)+ Jb (af 1 X) (af 2 Y) (Br 3))=
  p4 (Bm+(X+ Y))- p4 (Bm+(X- Y))- p4 (Bm+(Y- X))+ p4 (Bm+ -(X+ Y)):=by
  simp +decide only[Jb,Jj,p4,bu,Br,Bm,R5,W8,
   Aa,x0,l,x2,m,R8,R9]
  grind
 rw[h,i,j,k]at g;grind
def OB (c:ℂ) (C:c≠0) (X Z W Y:Jf)
 (dz:K4 (J (c•dv 1)) Z)
 (b:K4 (J (c•dv 1)) Y)
 (kX:K4 X Z)
 (a:K4 W Y)
 (n:hn 1 X+ hn 3 Z=0) (o:hn 1 W+ hn 2 Y=0)
 (F:Jw (J (Br 1)) Y Z+
  Jw W (J (Br 2)) Z+
  Jw X Y (J (Br 3))=0)
 (y:Md Z) (x:Md Y):False:=by
 have k:=dz 2;have u3:=dz 3;have l:=b 2;have m:=b 3;simp +decide only[J,dv,Q6,Q5,R8,R9]at k u3 l m;have B:Z 2=0:=by grind
 have z3:Z 3=0:=by grind
 have z:Y 2=0:=by grind
 have A:Y 3=0:=by grind
 have d:=kX 0;have e:=kX 1;have f:=kX 2;have g:=a 0;have i:=a 1;have j:=a 2;clear dz b kX a k u3 l m;simp +decide only[Jw,Md,U4,J,Br,Bm,hn,R8,R9,B,z3,z,A]
  at F n o d e f g i j y x
 have r:(X 0+ X 1+ X 2+ X 3)*(Z 0+ Z 1)=0:=by grind
 have s:X 0*Z 0=0:=by grind
 have t:X 1*Z 1=0:=by grind
 have u:(W 0+ W 1+ W 2+ W 3)*(Y 0+ Y 1)=0:=by grind
 have v:W 0*Y 0=0:=by grind
 have w:W 1*Y 1=0:=by grind
 clear d e f g i j;rcases Q3.1 r with h | h<;>rcases Q3.1 s with h2 | h2<;>rcases Q3.1 t with h3 | h3<;>
 rcases Q3.1 u with h4 | h4<;>rcases Q3.1 v with p | p<;>rcases Q3.1 w with q | q<;>grind
def Oj:JX 1:=by
 intro A a b h5 x y z l w h3;have k:D3 1 2 3:=by decide
 have f:D3 2 1 3:=by decide
 have j:D3 3 1 2:=by decide
 have ⟨c,n,g⟩:=Js A a b h5 1 2 3 k l (by grind)
 obtain⟨B,-⟩:=Jd A a h5 2 1;obtain⟨C,-⟩:=Jd A a h5 3 1;have ⟨X,d,p⟩:=pk A 2 3 (by grind)
 have ⟨Y,e,o⟩:=pk A 3 2 (by rw[T5];grind)
 have t:af 1 (Ju 1 (c•dv 1))=c•dv 1:=by funext q;simp[bu,Ju]
 have u:af 2 (Ju 1 (c•dv 1))=0:=by funext q;simp[bu,Ju]
 have v:af 3 (Ju 1 (c•dv 1))=0:=by funext q;simp[bu,Ju]
 have E2:Ju 1 (c•dv 1)∈Ar A 2:=(ei A 2 _).2 ⟨g,λq=> by simp[Ju]⟩
 have E3:Ju 1 (c•dv 1)∈Ar A 3:=(ei A 3 _).2 ⟨g,λq=> by simp[Ju]⟩
 have r:=Jn A a b h5 2 1 3 f y X d;have s:=Jn A a b h5 3 1 2 j z Y e;have h:=Ob A a b h5 2 1 3 f y X _ d E2 v;have i:=Ob A a b h5 3 1 2 j z Y _ e E3 u;rw[t]at h i;have m:=Oi A a b X Y d e;have D:=Jh (Br 1) (af 2 Y) (af 3 X);have E:=Jh (af 1 Y) (Br 2) (af 3 X);have F:=Jh (af 1 X) (af 2 Y) (Br 3);simp only[Jb]at m;exact OB c n (J (af 1 X)) (J (af 3 X)) (J (af 1 Y)) (J (af 2 Y))
  (Jk _ _ h) (Jk _ _ i)
  (Jk _ _ r) (Jk _ _ s) (F1 A a b 1 3 2 X d) (F1 A a b 1 2 3 Y e)
  (by grind) (Ja _ p) (Ja _ o)
def aaU: Prop := ∀ A:Sq,(∀ t∈A,p4 (Bm+ t)=65)->finrank ℂ A=5->(∀ X∈A,∀ j,X (0,j)=0)->False
def OC (e S1 S2 S3 i g j k a d c b:ℂ) (vS:S2=5*S1) (q:d=5*c)
 (y:8*e+19*(S1+ S2+ S3)-5*S1=0)
 (r:4*e*a=(e+ S1+ S2+ S3)*(a+ d+ c+ b))
 (s:4*S1*d=(e+ S1+ S2+ S3)*(a+ d+ c+ b))
 (t:4*S3*b=(e+ S1+ S2+ S3)*(a+ d+ c+ b))
 (u:4*i*a=(i+ g+ j+ k)*(a+ d+ c+ b))
 (v:4*g*d=(i+ g+ j+ k)*(a+ d+ c+ b))
 (w:4*j*c=(i+ g+ j+ k)*(a+ d+ c+ b))
 (x:4*k*b=(i+ g+ j+ k)*(a+ d+ c+ b))
 (f:8*i+19*(g+ j+ k)-5*g+(8*a+19*(d+ c+ b)-5*c)=0)
 (nS:e≠0\/S1≠0\/S2≠0\/S3≠0) (z:a≠0\/d≠0\/c≠0\/b≠0):False:=by
 subst vS q;by_cases p:c=0
 · subst p;have m:e*a=0:=by grind
   have p3:S3*b=0:=by grind
   have n:(e+6*S1+S3)*(a+b)=0:=by grind
   rcases Q3.1 m with h | h<;>rcases Q3.1 p3 with h' | h'<;>
    rcases Q3.1 n with l | l<;>grind
 by_cases o:S1=0
 · subst o;have m:e*a=0:=by grind
   have p3:S3*b=0:=by grind
   have n:(e+S3)*(a+6*c+b)=0:=by grind
   rcases Q3.1 m with h | h<;>rcases Q3.1 p3 with h' | h'<;>
    rcases Q3.1 n with l | l<;>grind
 grind
def Ok:J7 1:=by
 intro A a b h5 x y z F G v;have q:D3 1 2 3:=by decide
 have d:D3 3 1 2:=by decide
 have ⟨c,p,o⟩:=Js A a b h5 3 1 2 d v (by grind)
 obtain⟨H,-⟩:=Jd A a h5 1 2;obtain⟨L,-⟩:=Jd A a h5 2 1;obtain⟨M,-⟩:=Jd A a h5 3 1;obtain⟨-,-,-,-,E⟩:=Jd A a h5 1 2;have l:Ar A 1 ⊔ Ar A 2=A:=
  eq_of_le_of_finrank_eq (sup_le (I6 A 1) (I6 A 2)) (by grind)
 have ⟨T,h,nT⟩:=dk (K:=Ar A 2 ⊓ Ar A 3) (by grind)
 have ⟨X,hX,B⟩:=pk A 3 2 (by rw[T5];grind)
 have f:T∈Ar A 3:=h.2;have s:T∈A:=I6 A 3 f;have j:af 2 T=0:=JH h.1;have ns:af 1 T≠0:=λe=> nT ((JL A b 1 2 3 q T h).2 e)
 have i:=Jk _ _ (Ob A a b h5 3 1 2 d z X T hX f j);have kX:=Jk _ _ (Jn A a b h5 3 1 2 d z X hX);have m:=F1 A a b 1 2 3 T f;have u:hn 2 (J 0)=0:=by simp[hn,J]
 rw[j,u,S0]at m;have ⟨g,k,t,r,w⟩:=U5.1 (by rw[l];exact I6 A 3 hX:X∈Ar A 1 ⊔ Ar A 2)
 have D:af 2 X=af 2 g:=by
  rw[<- w,S4,show af 2 t=0 from JH r,S0]
 have vS:J (af 1 T) 2=5*J (af 1 T) 1:=by
  have e:=(SL A a b 3 1 2 d _ o T s).2.1;rw[j,JA,S0]at e;have n:=Jh (c•dv 3) (af 1 T) (Br 2);rw[show p4 (Jj (c•dv 3) (af 1 T) (Br 2))=0 from e]at n;simp +decide only[Jw,J,dv,Br,Bm,Q6,Q5,U4,
   R8,R9]at n ⊢
  apply mul_left_cancel₀ p;grind
 have C:J (af 2 X) 1=5*J (af 2 X) 2:=by
  have e:=(SL A a b 3 1 2 d _ o g (I6 A 1 k)).2.1;rw[show af 1 g=0 from JH k,Jm,Y0,<- D]at e;have n:=Jh (c•dv 3) (Br 1) (af 2 X);rw[show p4 (Jj (c•dv 3) (Br 1) (af 2 X))=0 from e]at n;simp +decide only[Jw,J,dv,Br,Bm,Q6,Q5,U4,
   R8,R9]at n ⊢
  apply mul_left_cancel₀ p;grind
 exact OC (J (af 1 T) 0) (J (af 1 T) 1) (J (af 1 T) 2) (J (af 1 T) 3)
  (J (af 1 X) 0) (J (af 1 X) 1) (J (af 1 X) 2) (J (af 1 X) 3)
  (J (af 2 X) 0) (J (af 2 X) 1) (J (af 2 X) 2) (J (af 2 X) 3) vS C m
  (i 0) (i 1) (i 3) (kX 0) (kX 1) (kX 2) (kX 3) (F1 A a b 1 2 3 X hX) (Ja _ ns) (Ja _ B)
def OD (S X Y:Jf)
 (l:K4 S Y)
 (kX:K4 X Y)
 (k:hn 1 S=0) (f:hn 1 X+ hn 2 Y=0) (x:hn 3 Y=0)
 (e:Jw (J (Br 1)) Y Y+
  Jw X (J (Br 2)) Y=0)
 (nS:Md S) (C:Md Y):False:=by
 have ⟨k0,g,i,j⟩:=JK l;have ⟨o,p,q,l3⟩:=JK kX;simp only[hn]at k f x;simp +decide only[Jw,U4,J,Br,Bm,R8,R9]at e;have G:4*((-7)*Y 0*Y 0+(-1)*Y 1*Y 1+(-5)*Y 2*Y 2+(-5)*Y 3*Y 3)+
  18*(Y 0+ Y 1+ Y 2+ Y 3)^2=0:=by grind
 by_cases hz:Y 0=0\/Y 1=0\/Y 2=0\/Y 3=0
 · have M:(S 0+ S 1+ S 2+ S 3)*(Y 0+ Y 1+ Y 2+ Y 3)=0:=by
    rcases hz with h | h | h | h
    .grind
    .grind
    .grind
    .grind
   have N:(X 0+ X 1+ X 2+ X 3)*(Y 0+ Y 1+ Y 2+ Y 3)=0:=by
    rcases hz with h | h | h | h
    .grind
    .grind
    .grind
    .grind
   have r:∀ m,Y m=0\/(S m=0/\X m=0):=λm=> by
    by_cases h:Y m=0
    .exact Or.inl h
    · exact Or.inr ⟨(Q3.1 (by grind:S m*Y m=0)).resolve_right h,
       (Q3.1 (by grind:X m*Y m=0)).resolve_right h⟩
   clear l kX k0 g i j o p q l3 e hz;rcases r 0 with a | ⟨a,D⟩<;>rcases r 1 with b | ⟨b,E⟩<;>rcases r 2 with c | ⟨c,F⟩<;>
    rcases r 3 with d | ⟨d,L⟩<;>grind
 push_neg at hz;have ⟨y0,t,u,v⟩:=hz;have hσ:S 0+ S 1+ S 2+ S 3≠0:=by
  intro h;rw[h,V6]at k0 g i j;have z:∀ s y:ℂ,y≠0->4*s*y=0->s=0:=λs y B w=>
   (Q3.1 ((Q3.1 w).resolve_right B)).resolve_left (by norm_num)
  rcases nS with n | n | n | n;exacts [n (z _ _ y0 k0),n (z _ _ t g),n (z _ _ u i),n (z _ _ v j)]
 have H:4*(Y 0*Y 1*Y 2*Y 3)=(Y 0+ Y 1+ Y 2+ Y 3)*
  (Y 1*Y 2*Y 3+ Y 0*Y 2*Y 3+ Y 0*Y 1*Y 3+ Y 0*Y 1*Y 2):=mul_left_cancel₀ hσ (by
  grind)
 have xm:∀ m,Y m≠0->(S 0+ S 1+ S 2+ S 3)*X m=(X 0+ X 1+ X 2+ X 3)*S m:=λm A=>
  mul_left_cancel₀ (mul_ne_zero (by norm_num :(4:ℂ)≠0) A) (by
   grind)
 have K:8*Y 0+19*(Y 1+ Y 2+ Y 3)-5*Y 2=0:=mul_left_cancel₀ hσ (by
  linear_combination (S 0+ S 1+ S 2+ S 3)*f-8*xm 0 y0-14*xm 1 t-19*xm 2 u-19*xm 3 v-
   (X 0+ X 1+ X 2+ X 3)*k)
 clear l kX k0 g i j o p q l3 e f k xm nS C hσ;grind
def OE (c:ℂ) (r:c≠0) (X Y T:Jf)
 (a:K4 (J (c•dv 1)) Y)
 (kX:K4 X Y)
 (f:hn 1 X+ hn 2 Y=0) (o:T 1=0) (i:hn 3 T=0)
 (pk:Jw (J (Br 2)) (J (c•dv 1)) T=0)
 (g:Jw (J (Br 1)) Y T+
  Jw X (J (Br 2)) T=0)
 (n:Md Y) (m:Md T):False:=by
 have e:=a 2;have u3:=a 3;simp +decide only[J,dv,Q6,Q5,R8,R9]at e u3;have p:Y 2=0:=by grind
 have q:Y 3=0:=by grind
 have b:=kX 0;have l1:=kX 1;have d:=kX 2;clear a kX e u3;simp +decide only[Jw,Md,U4,J,dv,Br,Bm,hn,Q6,Q5,
  R8,R9,p,q,o]at pk g f i b l1 d n m
 have j:(X 0+ X 1+ X 2+ X 3)*(Y 0+ Y 1)=0:=by grind
 have k:X 0*Y 0=0:=by grind
 have l:X 1*Y 1=0:=by grind
 clear b l1 d;rcases Q3.1 j with h | h<;>rcases Q3.1 k with h2 | h2<;>
  rcases Q3.1 l with h4 | h4<;>grind
def Ol:J7 2:=by
 intro A hA b j x y z h1 h2 M;have i:D3 1 2 3:=by decide
 have q:D3 2 1 3:=by decide
 have h:D3 3 1 2:=by decide
 obtain⟨k3,-⟩:=Jd A hA j 3 1;obtain⟨-,-,v2,-,-⟩:=Jd A hA j 2 1;have ⟨T,k,V⟩:=dk (K:=Ar A 2 ⊓ Ar A 3) (by grind)
 have ⟨X,hX,C⟩:=pk A 3 2 (by rw[T5];grind)
 have T3:T∈Ar A 3:=k.2;have G:af 2 T=0:=JH k.1;have g:=(JL A b 1 2 3 i T k).1;have B:af 1 T≠0:=λe=> V ((JL A b 1 2 3 i T k).2 e)
 have D:=Jn A hA b j 3 1 2 h z X hX;have kq:=Ob A hA b j 3 1 2 h z X T hX T3 G;have fT:=F1 A hA b 1 2 3 T T3;have s:∀ r,hn r (J 0)=0:=λr=> by simp[hn,J]
 rw[G,s,S0]at fT;have N:=(sw A b 3 1 2 h).trans M;have F:∀ E∈Ar A 1 ⊓ Ar A 2,af 1 E=0:=λE hE=>
  JH hE.1
 have z3:∀ v:Jf,Jb 0 v (Br 3)=0:=λv=> by rw[Ji];exact Jm _ _
 have m:∀ E∈Ar A 1 ⊓ Ar A 2,hn 3 (J (af 3 E))=0:=λE hE=> by
  have :=F1 A hA b 1 3 2 E hE.2;rwa[F E hE,s,Y0]at this
 have t:∀ E∈Ar A 1 ⊓ Ar A 2,Jb (Br 1) (af 2 X) (af 3 E)+ Jb (af 1 X) (Br 2) (af 3 E)=0:=
  λE hE=> by
   have d:=Oi A hA b E X hE.2 hX;rwa[F E hE,z3,S0]at d
 by_cases hy:af 2 X∈(Ar A 1 ⊓ Ar A 2).map (af 3)
 · have ⟨E,hE,n⟩:=hy;have d:=t E hE;rw[n]at d;have l:=m E hE;rw[n]at l;have S:=Jh (Br 1) (af 2 X) (af 2 X);have U:=Jh (af 1 X) (Br 2) (af 2 X);simp only[Jb]at d;exact OD _ _ _ (Jk _ _ kq) (Jk _ _ D) fT (F1 A hA b 1 2 3 X hX) l
    (by grind) (Ja _ B) (Ja _ C)
 have hPL:∀ u∈(Ar A 1 ⊓ Ar A 2).map (af 3),∀ w∈(Cn A).map (af 2),Jb (af 1 T) w u=0:=by
  rintro _ ⟨E,hE,rfl⟩ _ ⟨Z,P,rfl⟩;have o:JF 1 3 (af 1 T) (af 3 E)∈A:=by
   rw[<- Jq 1 3 (by decide)];exact A.add_mem g (JL A b 3 1 2 h E hE).1
  obtain⟨a,Q,w,p,rfl⟩:=U5.1 P;obtain⟨c,rfl⟩:=T8.1 p;have ⟨W,p2⟩:=PL A hA b 2 1 3 q _ _ o a Q;rw[S4,S5,Jv,Je,O,Ji,p2,Ji,W];grind
 have hK:=Oa (af 1 T) ((Ar A 1 ⊓ Ar A 2).map (af 3) ⊔ span ℂ {af 2 X})
  ((Cn A).map (af 2)) (by
   intro u R w p;obtain⟨u1,H,u2,hu2,rfl⟩:=U5.1 R;obtain⟨c,rfl⟩:=T8.1 hu2;rw[Jg,Jc,hPL u1 H w p,kq w];grind)
 have f:=du _ _ hy;have ⟨c,hc⟩:=Ox _ 1 2 3 i (SL A hA b 1 2 3 i _ g 0 A.zero_mem).1 (by grind)
 have L:c≠0:=λe=> B (by rw[hc,e,T9])
 obtain⟨_,⟨E,hE,rfl⟩,Y,tn⟩:=kv _ 1 N.ge;have o:JF 1 3 (af 1 T) (af 3 E)∈A:=by
  rw[<- Jq 1 3 (by decide)];exact A.add_mem g (JL A b 3 1 2 h E hE).1
 have pk:=(PL A hA b 2 1 3 q _ _ o 0 A.zero_mem).1;have d:=t E hE;rw[hc]at kq pk;have n0:=Jh (Br 2) (c•dv 1) (af 3 E);have S:=Jh (Br 1) (af 2 X) (af 3 E);have U:=Jh (af 1 X) (Br 2) (af 3 E);simp only[Jb]at d pk;exact OE c L _ _ _ (Jk _ _ kq) (Jk _ _ D) (F1 A hA b 1 2 3 X hX) Y (m E hE)
  (by grind) (by grind) (Ja _ C) (Ja _ tn)
def OL (X Q a:Jf) (j:K4 X Q)
 (k:K4 X a) (w:a 0=0)
 (y:Md X) (b:a 0≠0\/a 1≠0\/a 2≠0\/a 3≠0):
 Q 0*Q 1*Q 2*Q 3=0/\(Q 0+ Q 1+ Q 2+ Q 3)*
  (Q 0*Q 1*Q 2+ Q 0*Q 1*Q 3+ Q 0*Q 2*Q 3+ Q 1*Q 2*Q 3)=0:=by
 have ⟨p,q,r,s⟩:=JK j;have ⟨d,e,f,g⟩:=JK k;rw[w]at d e f g b;have i:(X 0+ X 1+ X 2+ X 3)*(a 1+ a 2+ a 3)=0:=by grind
 rcases Q3.1 i with h | h
 · have l:X 0*Q 0=0:=by grind
   have m:X 1*Q 1=0:=by grind
   have p2:X 2*Q 2=0:=by grind
   have p3:X 3*Q 3=0:=by grind
   clear p q r s d e f g j k i b;rcases Q3.1 l with c0 | c0<;>rcases Q3.1 m with c1 | c1<;>
    rcases Q3.1 p2 with c2 | c2<;>rcases Q3.1 p3 with c3 | c3<;>grind
 · have t:X 1*a 1=0:=by grind
   have u:X 2*a 2=0:=by grind
   have v:X 3*a 3=0:=by grind
   have o:X 1=0\/X 2=0\/X 3=0:=by
    rcases b with n | n | n | n
    .exact absurd rfl n
    .exact Or.inl ((Q3.1 t).resolve_right n)
    .exact Or.inr (Or.inl ((Q3.1 u).resolve_right n))
    .exact Or.inr (Or.inr ((Q3.1 v).resolve_right n))
   have x:(X 0+ X 1+ X 2+ X 3)*(Q 0+ Q 1+ Q 2+ Q 3)=0:=by
    rcases o with z | z | z
    .grind
    .grind
    .grind
   have l:X 0*Q 0=0:=by grind
   have m:X 1*Q 1=0:=by grind
   have p2:X 2*Q 2=0:=by grind
   have p3:X 3*Q 3=0:=by grind
   clear p q r s d e f g j k i b t u v o h;rcases Q3.1 x with c | c<;>rcases Q3.1 l with c0 | c0<;>
    rcases Q3.1 m with c1 | c1<;>rcases Q3.1 p2 with c2 | c2<;>
    rcases Q3.1 p3 with c3 | c3<;>grind
set_option maxHeartbeats 0 in
def On (Q P:Jf) (g:hn 3 Q=0) (e:hn 2 P=0)
 (d:Q 0*Q 1*Q 2*Q 3=0/\(Q 0+ Q 1+ Q 2+ Q 3)*
  (Q 0*Q 1*Q 2+ Q 0*Q 1*Q 3+ Q 0*Q 2*Q 3+ Q 1*Q 2*Q 3)=0)
 (c:P 0*P 1*P 2*P 3=0/\(P 0+ P 1+ P 2+ P 3)*
  (P 0*P 1*P 2+ P 0*P 1*P 3+ P 0*P 2*P 3+ P 1*P 2*P 3)=0)
 (f:Jw (J (Br 1)) P Q=0)
 (l:Md Q) (k:Md P):
 (Q 0=0/\Q 3=0/\Q 1+ Q 2=0/\P 1=0/\P 2=0/\8*P 0+19*P 3=0)\/
 (P 0=0/\P 2=0/\P 1+ P 3=0/\Q 1=0/\Q 3=0/\8*Q 0+19*Q 2=0):=by
 have ⟨b,eQ⟩:=d;have ⟨a,eP⟩:=c;simp only[hn]at g e;simp +decide only[Jw,U4,J,Br,Bm,R8,R9]at f;have j:Q 0=0\/Q 1=0\/Q 2=0\/Q 3=0:=by simpa only[Q3,or_assoc] using b
 have i:P 0=0\/P 1=0\/P 2=0\/P 3=0:=by simpa only[Q3,or_assoc] using a
 clear b a;rcases j with h | h | h | h<;>rcases i with h' | h' | h' | h'<;>
  simp only[h,h',T6,V6,S0,Y0,Q3]at eQ eP<;>
  rcases eQ with eQ | (eQ | eQ) | eQ<;>rcases eP with eP | (eP | eP) | eP<;>grind (splits :=16)
def OF (Q P X Z U W:Jf)
 (p:(Q 0=0/\Q 3=0/\Q 1+ Q 2=0/\P 1=0/\P 2=0/\8*P 0+19*P 3=0)\/
  (P 0=0/\P 2=0/\P 1+ P 3=0/\Q 1=0/\Q 3=0/\8*Q 0+19*Q 2=0))
 (a:K4 X Q)
 (kZ:K4 X Z)
 (kP:K4 U P)
 (b:K4 U W)
 (k:Jw (J (Br 1)) W Q+
  Jw U (J (Br 2)) Q=0)
 (gX:Jw (J (Br 1)) P Z+
  Jw X P (J (Br 3))=0)
 (t:Md Q) (s:Md P)
 (v:Md X) (u:Md U):False:=by
 simp +decide only[Jw,U4,J,Br,Bm,R8,R9]at k gX;rcases p with⟨l,r,m,d,n,c⟩ | ⟨l,q,m,d,o,c⟩
 · have g:=kP 0;have u1:=kP 1;have u3:=kP 3;have i:=b 1;have j:=b 2;clear a kZ kP b gX;have e:(U 0+ U 1+ U 2+ U 3)*(P 0+ P 3)=0:=by
    rw[d,n]at u1;grind
   have f:P 0≠0:=λh=> by rw[h]at c;grind
   have hs:U 0+ U 1+ U 2+ U 3=0:=(Q3.1 e).resolve_right (λh=> f (by grind))
   rw[hs,V6]at g u3 i j;grind
 · have g:=a 0;have u1:=a 1;have u3:=a 2;have i:=kZ 1;have j:=kZ 3;clear a kZ kP b k;have e:(X 0+ X 1+ X 2+ X 3)*(Q 0+ Q 2)=0:=by
    rw[d,o]at u1;grind
   have f:Q 0≠0:=λh=> by rw[h]at c;grind
   have hs:X 0+ X 1+ X 2+ X 3=0:=(Q3.1 e).resolve_right (λh=> f (by grind))
   rw[hs,V6]at g u3 i j;grind
def Oo:JX 0:=by
 intro A hA h0 g x y z h1 h2 h3;have B:D3 2 1 3:=by decide
 have H:D3 3 1 2:=by decide
 obtain⟨k2,-⟩:=Jd A hA g 2 1;obtain⟨k3,-⟩:=Jd A hA g 3 1;have q2:=Pa A hA h0 g 2 1 3 B y (by grind)
 have q3:=Pa A hA h0 g 3 1 2 H z (by grind)
 rw[T5 (Ar A 2) (Ar A 1)]at q2;rw[T5 (Ar A 3) (Ar A 1),T5 (Ar A 3) (Ar A 2)]at q3;have ⟨T3,l,R⟩:=dk (K:=Ar A 1 ⊓ Ar A 2) (by grind)
 have ⟨T2,k,Q⟩:=dk (K:=Ar A 1 ⊓ Ar A 3) (by grind)
 have ⟨X,m,G⟩:=pk A 2 1 (by rw[T5];grind)
 have ⟨Y,n,F⟩:=pk A 3 1 (by rw[T5];grind)
 have i:=l.2;have h:=k.2;have r3:af 1 T3=0:=JH l.1;have r2:af 1 T2=0:=JH k.1;have p:af 3 T3≠0:=λe=> R ((JL A h0 3 1 2 H T3 l).2 e)
 have o:af 2 T2≠0:=λe=> Q ((JL A h0 2 1 3 B T2 k).2 e)
 have z1:∀ v w:Jf,Jb 0 v w=0:=λv w=> by rw[Ji];exact Jm _ _
 have M:∀ r,hn r (J 0)=0:=λr=> by simp[hn,J]
 have S:=Jn A hA h0 g 2 1 3 B y X m;have kq:∀ w,Jb (af 1 X) w (af 3 T3)=0:=λw=>
  (JP _ _ _).trans (Ob A hA h0 g 2 3 1 (by decide) y X T3 m i r3 w)
 have T:=Jn A hA h0 g 3 1 2 H z Y n;have E:∀ w,Jb (af 1 Y) w (af 2 T2)=0:=λw=>
  (JP _ _ _).trans (Ob A hA h0 g 3 2 1 (by decide) z Y T2 n h r2 w)
 have L:=Bj.1 h1;have kv2:∀ (u v s:Fq->ℂ),u≠0->v∉ span ℂ {u}->(∀ w,Jb s w u=0)->
  (∀ w,Jb s w v=0)-> ∃ a:Jf,(∀ w,Jb s w a=0)/\J a 0=0/\a≠0:=by
  intro u v s hu hv ku P;have hK:=Oa s (span ℂ {u} ⊔ span ℂ {v}) ⊤ (by
   intro t ht w _;obtain⟨a,ha,b,hb,rfl⟩:=U5.1 ht;obtain⟨c,rfl⟩:=T8.1 ha;obtain⟨d,rfl⟩:=T8.1 hb;rw[Jg,Jc,Jc,ku w,P w];grind)
  have f:=du _ _ hv;rw[Ab hu]at f;rw[finrank_top,As]at hK;exact J4 s 0 (by grind)
 have ⟨a,ka,U,na⟩:=kv2 _ (af 3 X) _ p (λD=> by
  have ⟨c,C⟩:=T8.1 D;have j:X- c•T3∈Ar A 2 ⊓ Ar A 3:=W7.2 ⟨(Ar A 2).sub_mem m ((Ar A 2).smul_mem c i),
   (ei A 3 _).2 ⟨A.sub_mem (I6 A 2 m) (A.smul_mem c (I6 A 2 i)),λq=> by
    have :=congrFun C q;simp only[bu,Q6,Q5]at this;simp only[W8,Q6,Q5];grind⟩⟩
  rw[L]at j;apply G;funext q;have e:=congrFun ((Av ℂ).1 j) (1,q);have t:=congrFun r3 q;simp only[bu,W8,Q6,Q5,W0]at e t ⊢;rw[t,T6,X4]at e;exact e) kq S
 have ⟨b,kb,V,nb⟩:=kv2 _ (af 2 Y) _ o (λD=> by
  have ⟨c,C⟩:=T8.1 D;have j:Y- c•T2∈Ar A 2 ⊓ Ar A 3:=W7.2 ⟨(ei A 2 _).2 ⟨A.sub_mem (I6 A 3 n)
   (A.smul_mem c (I6 A 3 h)),λq=> by
    have :=congrFun C q;simp only[bu,Q6,Q5]at this;simp only[W8,Q6,Q5];grind⟩,
   (Ar A 3).sub_mem n ((Ar A 3).smul_mem c h)⟩
  rw[L]at j;apply F;funext q;have e:=congrFun ((Av ℂ).1 j) (1,q);have t:=congrFun r2 q;simp only[bu,W8,Q6,Q5,W0]at e t ⊢;rw[t,T6,X4]at e;exact e) E T
 have Z:=OL _ _ _ (Jk _ _ kq) (Jk _ _ ka) U (Ja _ G) (Ja _ na);have W:=OL _ _ _ (Jk _ _ E) (Jk _ _ kb) V (Ja _ F) (Ja _ nb);have O:=F1 A hA h0 1 3 2 T3 i;rw[r3,M,Y0]at O;have N:=F1 A hA h0 1 2 3 T2 h;rw[r2,M,Y0]at N;have fQP:=Oi A hA h0 T3 T2 i h;have fQY:=Oi A hA h0 T3 Y i n;have fXP:=Oi A hA h0 X T2 m h;rw[r2,r3,z1,z1,S0,S0]at fQP;rw[r3,z1,S0]at fQY;rw[r2,z1,S0]at fXP;simp only[Jb]at fQP fQY fXP;have n1:=Jh (Br 1) (af 2 T2) (af 3 T3);have n2:=Jh (Br 1) (af 2 Y) (af 3 T3);have n3:=Jh (af 1 Y) (Br 2) (af 3 T3);have n4:=Jh (Br 1) (af 2 T2) (af 3 X);have n5:=Jh (af 1 X) (af 2 T2) (Br 3);exact OF _ _ _ _ _ _ (On _ _ O N Z W (by grind) (Ja _ p) (Ja _ o))
  (Jk _ _ kq) (Jk _ _ S) (Jk _ _ E) (Jk _ _ T) (by grind)
  (by grind) (Ja _ p) (Ja _ o) (Ja _ G) (Ja _ F)
def Lm (t:Jf):(Fq->ℂ)→ₗ[ℂ] (Fq->ℂ) where
 toFun u m:=Jb t (Pi.single m 1) u
 map_add' u v:=funext λm=> Jg _ _ _ _
 map_smul' c u:=by funext m;simp only[Q6,Q5,Cg];exact Jc _ _ _ _
def OM (t u:Jf) (h:Lm t u=0) (x:Jf):Jb t x u=0:=by
 have a:x=x 0•Pi.single 0 1+ x 1•Pi.single 1 1+ x 2•Pi.single 2 1+ x 3•Pi.single 3 1:=by
  funext q;rcases f4 q with rfl | rfl | rfl | rfl<;>simp
 have z:∀ m,Jb t (Pi.single m 1) u=0:=λm=> congrFun h m
 rw[a,Je,Je,Je,O,O,O,O,z,z,z,z];grind
def Op (s a:Jf):∃ c:ℂ,∃ k:Jf,k≠0/\
 ((∀ x,Jb a x k=0)\/ ∀ x,Jb (s- c•a) x k=0):=by
 by_cases b:Function.Injective (Lm a)
 · obtain⟨c,f⟩:=Module.End.exists_eigenvalue
    ((LinearEquiv.ofInjectiveEndo (Lm a) b).symm.toLinearMap∘ₗ Lm s)
   have ⟨v,hv⟩:=Module.End.HasEigenvalue.exists_hasEigenvector f;have d:=congrArg (LinearEquiv.ofInjectiveEndo (Lm a) b) (Module.End.HasEigenvector.apply_eq_smul hv);simp only[Al,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,S5,
    LinearEquiv.coe_ofInjectiveEndo]at d
   refine⟨c,v,(Module.End.hasEigenvector_iff.1 hv).2,Or.inr (OM _ _ ?_)⟩;funext m;have e:=congrFun d m;simp only[Lm,Ac,Ad,Q6,Q5,W0]at e ⊢;rw[sub_eq_add_neg,<- neg_smul,Jp,Jt,e];grind
 .rw[<- LinearMap.ker_eq_bot]at b;have ⟨v,hv,g⟩:=Y7 b;exact⟨0,v,g,Or.inl (OM _ _ (Ak.1 hv))⟩
def OG (A:Sq) (hA:LV A) (h0:R0 A)
 (i:finrank ℂ A=5) (R:finrank ℂ (Ar A 2)=2) (o:finrank ℂ (A.map (af 2))=3)
 (p:finrank ℂ (A.map (af 3))=3) (s:Jf) (q:Ju 1 s∈A) (k:Jf) (n:k≠0)
 (t:∀ x,Jb s x k=0):∃ c:ℂ,s=c•dv 1:=by
 have Kr:D3 1 2 3:=by decide
 obtain⟨-,-,P,c6,-⟩:=Jd A hA i 2 3;obtain⟨-,-,Q,-,-⟩:=Jd A hA i 3 2;have M:(Cn A).map (af 2)= ⊤ :=Bl (by rw[P,o];simp)
 have N:(Cn A).map (af 3)= ⊤ :=Bl (by rw[Q,p];simp)
 obtain⟨e,l,rfl⟩:=mem_map.1 (M ▸ Au:k∈(Cn A).map (af 2));have ne:e∉ Ar A 2:=λh=> n (JH h)
 have y:=Ov A hA h0 1 2 3 Kr s q;have f:∀ r∈Ar A 2 ⊔ span ℂ {e},∀ z∈Cn A,Om s 2 3 r z=0:=by
  intro r f z _;obtain⟨r1,C,T,D,rfl⟩:=U5.1 f;obtain⟨c,rfl⟩:=T8.1 D;show Jb s (af 2 (r1+ c•e)) (af 3 z)=0;rw[S4,S5,show af 2 r1=0 from JH C,Y0,
   O,Jl,t,T6]
 have hRC:Ar A 2 ⊔ span ℂ {e}≤ Cn A:=
  sup_le (le_trans (I6 A 2) Ce) ((Bf _ _).2 l)
 have S:=du (Ar A 2) e ne;have ⟨e',m,v,g⟩:=OJ (Om s 2 3) (Cn A) _ hRC y f (Or.inr (by grind))
 have kk':∀ x,Jb s x (af 2 e')=0:=λx=> by
  obtain⟨z,L,rfl⟩:=mem_map.1 (N ▸ Au:x∈(Cn A).map (af 3));have h:=g z L;simp only[Om,LinearMap.mk₂_apply]at h;rw[Jl];exact h
 have ind:af 2 e'∉ span ℂ {af 2 e}:=by
  intro J;have ⟨c,G⟩:=T8.1 J;apply v;have H:e'- c•e∈Ar A 2:=gl A hA 2 _ ((Cn A).sub_mem m ((Cn A).smul_mem c l))
   (by rw[V8,S5,G,Aj])
  rw[show e'=(e'- c•e)+ c•e by abel]
  exact V7 _ (X7 H)
   (Y2 (T4 _ _ (Y6 _)))
 have j:=Oa s (span ℂ {af 2 e} ⊔ span ℂ {af 2 e'}) ⊤ (by
  intro u K w _;obtain⟨a,E,b,F,rfl⟩:=U5.1 K;obtain⟨c,rfl⟩:=T8.1 E;obtain⟨d,rfl⟩:=T8.1 F;rw[Jg,Jc,Jc,t w,kk' w];grind)
 have B:=du _ _ ind;rw[Ab n]at B;rw[finrank_top,As]at j;exact Ox s 1 2 3 Kr (SL A hA h0 1 2 3 Kr s q 0 A.zero_mem).1 (by grind)
def OH (c:ℂ) (C:c≠0) (W:Jf) (H:Fq->Fq->ℂ)
 (a:∀ k l:Fq,Jw (J (c•dv 1)) (J (Pi.single k 1)) (H l)+
  Jw (J (c•dv 1)) (J (Pi.single l 1)) (H k)=0)
 (b:∀ k l:Fq,Jw W (J (Pi.single k 1)) (H l)+
  Jw W (J (Pi.single l 1)) (H k)=0)
 (o:∀ m,Bm (2,0)*H 0 m+ Bm (2,1)*H 1 m+ Bm (2,2)*H 2 m+ Bm (2,3)*H 3 m=J (Br 3) m)
 (B:hn 1 W=0) (D:W 0≠0\/W 1≠0\/W 2+ W 3≠0):False:=by
 have a00:=a 0 0;have d:=a 0 1;have e:=a 0 2;have f:=a 0 3;have u:=a 1 1;have g:=a 1 2;have r:=a 1 3;have v:=a 2 2;have s:=a 2 3;have h:=a 3 3;have w:=b 0 0;have q:=b 0 1;have p:=b 0 2;have t:=b 0 3;have i:=b 1 1;have j:=b 1 2;have b13:=b 1 3;have b22:=b 2 2;have b23:=b 2 3;have n:=b 3 3;have ⟨x,y,z,A⟩:=JK o;clear a b o;simp +decide only[Jw,U4,J,dv,Q4,Q6,Q5,
  Br,Bm,hn,R8,R9]at a00 d e f u g r v s h w q p t i j b13 b22 b23 n x y z A B
 grind
def Oq:JX 2:=by
 intro A b h0 h5 x y z R h2 h3;have o:D3 1 2 3:=by decide
 obtain⟨k2,-⟩:=Jd A b h5 2 1;obtain⟨-,-,v2,-,-⟩:=Jd A b h5 2 1;have U:Ar A 2≤ Ar A 3:=inf_eq_left.1 (eq_of_le_of_finrank_eq inf_le_left (by grind))
 have t:=(sw A h0 1 2 3 o).trans R;have C:∀ u∈(Ar A 2 ⊓ Ar A 3).map (af 1),Ju 1 u∈A:=by
  rintro _ ⟨T,g,rfl⟩;exact (JL A h0 1 2 3 o T g).1
 have ⟨B,d,j⟩:=Y7 (p:=(Ar A 2 ⊓ Ar A 3).map (af 1))
  (by intro V;rw[V,V3]at t;grind)
 have ⟨s,Y,ns⟩:=At (Z9
  ((Bf _ _).2 d) (λe=> by rw[<- e,Ab j]at t;grind))
 obtain⟨μ,k,W,K⟩:=Op s B;have ⟨i,hs0,n0,k0⟩:∃ i∈(Ar A 2 ⊓ Ar A 3).map (af 1),i≠0/\ ∀ x,Jb i x k=0:=by
  rcases K with h | h
  .exact⟨B,d,j,h⟩
  · refine⟨s- μ•B,Ai _ Y (T4 _ _ d),λe=> ns ?_,h⟩
    rw[Bn.1 e];exact T4 _ _ (Y6 _)
 have ⟨c,hc⟩:=OG A b h0 h5 (by grind) y z i (C _ hs0) k W k0
 have E:c≠0:=λe=> n0 (by rw[hc,e,T9])
 have G:dv 1∈(Ar A 2 ⊓ Ar A 3).map (af 1):=by
  have :=T4 _ c⁻¹ hs0;rwa[hc,Ae,V9 E,Aw]at this
 have ⟨w,H,nw⟩:=At (Z9 ((Bf _ _).2 G)
  (λe=> by
   rw[<- e,Ab (show dv 1≠0 from λh=> by simpa[dv] using congrFun h 2)]at t;grind))
 have nW:J w 0≠0\/J w 1≠0\/J w 2+ J w 3≠0:=by
  by_contra hn;push_neg at hn;have ⟨n0,n1,n2⟩:=hn;apply nw;simp +decide only[J,R8,R9]at n0 n1 n2;have L:w 0=0:=by grind
  have M:w 1=0:=by grind
  have N:w 3= -w 2:=by grind
  refine T8.2 ⟨w 2,funext λq=> ?_⟩
  rcases f4 q with rfl | rfl | rfl | rfl<;>simp +decide [dv,L,M,N]
 have sw:=C w H;have O:∀ r,hn r (J 0)=0:=λr=> by simp[hn,J]
 have F:hn 1 (J w)=0:=by
  obtain⟨T,g,rfl⟩:=H;have f:=F1 A b h0 1 2 3 T g.2;rwa[show af 2 T=0 from JH g.1,O,S0]at f
 have t2:(Cn A).map (af 2)= ⊤ :=Bl (by rw[v2,y];simp)
 choose Z a D using λk:Fq=>
  mem_map.1 (t2 ▸ Au:(Pi.single k 1:Jf)∈(Cn A).map (af 2))
 have n:∀ u,Ju 1 u∈A-> ∀ k l:Fq,
  Jb u (Pi.single k 1) (af 3 (Z l))+ Jb u (Pi.single l 1) (af 3 (Z k))=0:=by
  intro u hu k l;have Mq:=Ov A b h0 1 2 3 o u hu;have e:=Mq _ ((Cn A).add_mem (a k) (a l));have P:=Mq _ (a k);have Q:=Mq _ (a l);simp only[Om,LinearMap.mk₂_apply,S4,Z2,D,Je,Jg]at e P Q;grind
 have X:Bm-(Bm (2,0)•Z 0+ Bm (2,1)•Z 1+ Bm (2,2)•Z 2+ Bm (2,3)•Z 3)∈Ar A 3:=
  U (gl A b 2 _ ((Cn A).sub_mem (Y2 (Y6 _))
   ((Cn A).add_mem ((Cn A).add_mem ((Cn A).add_mem ((Cn A).smul_mem _ (a 0)) ((Cn A).smul_mem _ (a 1)))
    ((Cn A).smul_mem _ (a 2))) ((Cn A).smul_mem _ (a 3))))
   (by
    funext q;simp only[V8,S4,S5,Jv,D,W8,R5,Q6,Q5];rcases f4 q with rfl | rfl | rfl | rfl<;>simp[Br,Bm,Q4]))
 have r3:af 3 (Bm-(Bm (2,0)•Z 0+ Bm (2,1)•Z 1+ Bm (2,2)•Z 2+ Bm (2,3)•Z 3))=0:=
  JH X
 have S:∀ m,Bm (2,0)*J (af 3 (Z 0)) m+ Bm (2,1)*J (af 3 (Z 1)) m+
  Bm (2,2)*J (af 3 (Z 2)) m+ Bm (2,3)*J (af 3 (Z 3)) m=J (Br 3) m:=by
  intro m;have h:=congrArg (λv=> J v m) r3
  rcases f4 m with rfl | rfl | rfl | rfl<;>
   simp +decide only[J,V8,S4,S5,Jv,W8,
    R5,Q6,Q5,W0,R8,R9]at h ⊢ <;>
   grind
 exact OH c E (J w) (λl=> J (af 3 (Z l)))
  (λk l=> by
   beta_reduce;have h:=n (c•dv 1) (by rw[<- hc];exact C _ hs0) k l
   simp only[Jb]at h;have n1:=Jh (c•dv 1) (Pi.single k 1) (af 3 (Z l));have n2:=Jh (c•dv 1) (Pi.single l 1) (af 3 (Z k));grind)
  (λk l=> by
   beta_reduce;have h:=n w sw k l;simp only[Jb]at h;have n1:=Jh w (Pi.single k 1) (af 3 (Z l));have n2:=Jh w (Pi.single l 1) (af 3 (Z k));grind)
  S F nW
def afX:aaU:=λA d c h0=> Oz (J9 λs a b=> by interval_cases s;exacts [Ok,Ol])
 (J8 λs a=> by interval_cases s;exacts [Oo,Oj,Oq]) A d h0 c
end P5zS
abbrev K5 (L:Sq): Prop := ∀ t∈L,p4 (Bm+ t)=65
def d9 (u v:Fq->ℂ):Mt:=λq=> u q.1*v q.2
def r0 (X:Mt):Fq->ℂ:=λj=> X (0,j)
def NK (x:Fq):ℂ:=if x=2 then -1 else 1
def hv (p q:Fq->ℂ) (c x:Fq):ℂ:=
 if x=c then 0 else NK x*(p (cr c x 0)*q (cr c x 1)- p (cr c x 1)*q (cr c x 0))
def sg (p q:Fq->ℂ) (c:Fq):ℂ:= ∑ j,Bm (0,j)*hv p q c j
def um (s t:ℂ) (c x:Fq):Fq->ℂ:=λj=> if j=c then s else if j=x then -t else 0
def agd (c:Fq) (d:c.val<2) (p q y:Fq->ℂ) (a b:ℂ)
  (hy:∀ j,y j=a*p j+ b*q j): ∑ j,hv p q c j*y j=0:=by
 have :=hy 0;have :=hy 1;have :=hy 2;have :=hy 3;fin_cases c<;>simp_all[hv,cr,NK,U4]<;>ring
def akD (c:Fq) (h:c.val<2) (p q:Fq->ℂ) (hp:p c=0) (l:q c=0)
  (b:∀ s t:ℂ,s•p+ t•q=0->s=0/\t=0):∃ x,hv p q c x≠0:=by
 by_contra hn;push_neg at hn
 have k:∀ j m,q j*p m- p j*q m=0:=by
  have d:=hn 0;have e:=hn 1;have f:=hn 2;have g:=hn 3;intro j m;fin_cases c<;>simp[hv,cr,NK]at d e f g h<;>fin_cases j<;>fin_cases m<;>
   simp[hp,l]<;>grind
 obtain⟨j,i⟩:∃ j,p j≠0:=by
  by_contra a;push_neg at a
  exact one_ne_zero (b 1 0 (by funext m;simp[a m])).1
 exact i (Bk.1 (b (q j) (-p j) (by
  funext m;simp only[R5,Q6,Q5,W0];linear_combination k j m)).2)
def aei (L:Sq) (c:Fq) (q:c.val<2) (r:finrank ℂ (L.map (af 0))=2)
  (k:∀ X∈L,X (0,c)=0):∃ X1∈L,∃ X2∈L,
   (∀ X∈L,∃ a b:ℂ,∀ j,X (0,j)=a*X1 (0,j)+ b*X2 (0,j))/\ ∃ x,hv (r0 X1) (r0 X2) c x≠0:=by
 let B:=Module.finBasisOfFinrankEq ℂ (L.map (af 0)) r;obtain⟨X1,e,n⟩:=Af.1 (B 0).2;obtain⟨X2,f,o⟩:=Af.1 (B 1).2
 have l:∀ j,X1 (0,j)=(B 0:Fq->ℂ) j:=λj=> by rw[<- n,bu]
 have m:∀ j,X2 (0,j)=(B 1:Fq->ℂ) j:=λj=> by rw[<- o,bu]
 refine⟨X1,e,X2,f,λX p=> ?_,akD c q _ _ (k X1 e) (k X2 f) λs t i=> ?_⟩
 .have d:af 0 X∈L.map (af 0):=S8 p;have h:=B.sum_repr ⟨af 0 X,d⟩;rw[Ag]at h
  refine⟨B.repr ⟨af 0 X,d⟩ 0,B.repr ⟨af 0 X,d⟩ 1,λj=> ?_⟩
  have :=congrFun (congrArg Subtype.val h) j;simp only[Submodule.coe_add,Submodule.coe_smul,R5,Q6,Q5,bu]at this;rw[l,m,<- this]
 .have g:=Ax.1 B.linearIndependent ![s,t] (by
   apply Subtype.ext;funext j;have :=congrFun i j;simp only[r0,R5,Q6,Q5,W0,l,m]at this;simpa[Ag] using this)
  exact⟨by simpa using g 0,by simpa using g 1⟩
def ak4 (c x:Fq) (b:c.val<2) (a:x≠c) (p q:Fq->ℂ):
  hv p q c x*Bm (0,x)+ NK x*(Bm (0,cr c x 1)*q (cr c x 0)- Bm (0,cr c x 0)*q (cr c x 1))*p x
   + NK x*(Bm (0,cr c x 0)*p (cr c x 1)- Bm (0,cr c x 1)*p (cr c x 0))*q x=sg p q c:=by
 fin_cases c<;>fin_cases x<;>simp_all[sg,hv,cr,NK,Bm,U4]<;>ring
def Pq:∀ c x j:Fq,x≠c->j=c\/j=x\/j=cr c x 0\/j=cr c x 1:=by decide
def acX:∀ c x:Fq,x≠c->cr c x 0≠c/\cr c x 1≠c/\cr c x 0≠x/\cr c x 1≠x:=by decide
def aje (L:Sq) (H:K5 L) (G:finrank ℂ ↥(Ar L 0)=4)
  (c:Fq) (K:c.val<2) (l:∀ X∈L,X (0,c)=0) (a b:Mt) (s:a∈L) (t:b∈L)
  (x:Fq) (hx:hv (r0 a) (r0 b) c x≠0):
  (∃ W∈L,∀ j,j≠c->W (0,j)=(if j=x then sg (r0 a) (r0 b) c else 0)- hv (r0 a) (r0 b) c x*Bm (0,j))/\
  ∃ u:Fq->ℂ,u 0=0/\u≠0/\d9 u (um (hv (r0 a) (r0 b) c x*Bm (0,c)) (sg (r0 a) (r0 b) c) c x)∈L:=by
 have d:x≠c:=by intro e;apply hx;simp[hv,e]
 obtain⟨P,Q,y,z⟩:=acX c x d;set p:=r0 a;set q:=r0 b;set D:=hv p q c x
 have f:D=NK x*(p (cr c x 0)*q (cr c x 1)- p (cr c x 1)*q (cr c x 0)):=by simp[D,hv,d]
 have w:Bm (0,c)≠0:=by unfold Bm;split_ifs<;>norm_num
 have S:NK x*NK x=1:=by unfold NK;split_ifs<;>norm_num
 set W:Mt:=(NK x*(Bm (0,cr c x 1)*q (cr c x 0)- Bm (0,cr c x 0)*q (cr c x 1)))•a+
  (NK x*(Bm (0,cr c x 0)*p (cr c x 1)- Bm (0,cr c x 1)*p (cr c x 0)))•b
 have hW:W∈L:=L.add_mem (L.smul_mem _ s) (L.smul_mem _ t);set Y:Mt:=D•Bm+ W;have v:Y∈L ⊔ span ℂ {Bm}:=
  V0.2 ⟨W,hW,D•Bm,T4 _ _ (Ay Bm),Bo _ _⟩
 have eY:∀ j,Y (0,j)=D*Bm (0,j)+(NK x*(Bm (0,cr c x 1)*q (cr c x 0)- Bm (0,cr c x 0)*q (cr c x 1)))*p j+
   (NK x*(Bm (0,cr c x 0)*p (cr c x 1)- Bm (0,cr c x 1)*p (cr c x 0)))*q j:=λj=> by simp[Y,W,p,q,r0];ring
 have m:Y (0,c)=D*Bm (0,c):=by rw[eY];simp[p,q,r0,l a s,l b t]
 have C:Y∉ L:=λh=> mul_ne_zero hx w (m ▸ l Y h)
 have o:Y (0,cr c x 0)=0:=by rw[eY,f];ring
 have r:Y (0,cr c x 1)=0:=by rw[eY,f];ring
 have g:Y (0,x)=sg p q c:=by rw[eY];exact ak4 c x K d p q
 refine⟨⟨W,hW,λj N=> ?_⟩,?_⟩
 .have e:W (0,j)=Y (0,j)- D*Bm (0,j):=by simp[Y]
  rw[e];rcases Pq c x j d with rfl | rfl | rfl | rfl
  .exact absurd rfl N
  .rw[g];simp
  .rw[o];simp[y]
  .rw[r];simp[z]
 obtain⟨Z,J,F,Wj⟩:=B2L L H G c x (Ne.symm d) (D*Bm (0,c)) (sg p q c) Y v C o r m g;obtain⟨E,n⟩:=(ei L 0 Z).1 J
 have key:∀ i j,(D*Bm (0,c))*Z (i,j)=Z (i,c)*um (D*Bm (0,c)) (sg p q c) c x j:=by
  intro i j;rcases Ck i with M | ⟨k,rfl⟩
  .subst M;simp[n]
  .have A:=congrFun Wj (k,0);have B:=congrFun Wj (k,1);have R:=congrFun Wj (k,2);simp[sl]at A B R;rcases Pq c x j d with rfl | rfl | rfl | rfl
   .simp[um];ring
   .simp[um,d];grind
   .simp[um,P,y,A]
   .simp[um,Q,z,B]
 refine⟨λi=> Z (i,c),n c,λO=> F ?_,?_⟩
 .funext ⟨i,j⟩;have :=key i j
  rw[show Z (i,c)=0 from congrFun O i,V6]at this
  exact (Q3.1 this).resolve_left (mul_ne_zero hx w)
 .have e:d9 (λi=> Z (i,c)) (um (D*Bm (0,c)) (sg p q c) c x)=(D*Bm (0,c))•Z:=by
   funext ⟨i,j⟩;simp only[d9,Q6,Q5];rw[key i j]
  rw[e];exact L.smul_mem _ E
def pB (l c x:Fq):ℂ:=Bm (0,cr c x 0)*Bm (l,cr c x 1)+ Bm (0,cr c x 1)*Bm (l,cr c x 0)
def Qq (c x:Fq) (u:Fq->ℂ):ℂ:=pB 3 c x*u 1*u 2+ pB 2 c x*u 1*u 3+ pB 1 c x*u 2*u 3
def Cf (u v:Fq->ℂ):ℂ:=v 1*(u 2*u 3)+ v 2*(u 1*u 3)+ v 3*(u 1*u 2)
def Mf (u:Fq->ℂ) (j:Fq):ℂ:=u 1*MU 1 j+ u 2*MU 2 j+ u 3*MU 3 j
def cz (a b c u1 u2 u3:ℂ) (g:a≠0) (h:b≠0) (i:c≠0) (j:a*u1*u2+ b*u1*u3+ c*u2*u3=0):
  (u1≠0/\u2≠0/\u3≠0)\/(u2=0/\u3=0)\/(u1=0/\u3=0)\/(u1=0/\u2=0):=by
 by_cases d:u1=0<;>by_cases e:u2=0<;>by_cases f:u3=0<;>simp_all
def LK (l c x:Fq):pB l c x≠0:=by unfold pB Bm;split_ifs<;>norm_num
def RI (c x:Fq) (d:c.val<2) (f:x≠c) (u:Fq->ℂ) (e:u 0=0) (s t:ℂ)
  (h:∀ r:ℂ,p4 (Bm+ r•d9 u (um s t c x))=65):s*t*Qq c x u=0/\s*Mf u c=t*Mf u x:=by
 have a:=h 1;have b:=h (-1);fin_cases c<;>fin_cases x<;>simp at d f<;>
  simp +decide only[p4,d9,um,Bm,Qq,pB,Mf,MU,cr,R5,Q6,
   Q5,e,R8,R9,Fin.isValue,Fin.reduceAdd]at a b ⊢ <;>
  exact⟨by linear_combination (a+ b)/(-4),by linear_combination (a- b)/2⟩
def m3w (L:Sq) (a:K5 L) (X:Mt) (b:X∈L) (d:∀ j,X (0,j)=0):
  ∑ c,Bm (0,c)*m3 0 c X=0:=by
 have k:=ajd 0 Bm X d;rw[a _ (L.smul_mem _ b),a _ (L.smul_mem _ b),a _ (L.smul_mem _ b)]at k
 have e:p4 Bm=65:=by simpa using a 0 L.zero_mem
 rw[e]at k;grind
lemma aa2 (L:Sq) (g:K5 L) (c x z:Fq) (l:c.val<2) (m:x≠c)
  (n:z≠c) (k:x≠z) (u v:Fq->ℂ) (d:u 0=0) (hv:v 0=0) (s t i e:ℂ)
  (hR:d9 u (um s t c x)∈L) (f:d9 v (um i e c z)∈L):
  s*t*e*Cf u v=0/\i*t*e*Cf v u=0:=by
 have z0:∀ (w:Fq->ℂ) a j,w 0=0->d9 w a (0,j)=0:=λw a j h=> by simp[d9,h]
 have m1:=m3w L g _ (L.add_mem hR f) λj=> by simp[z0 u _ j d,z0 v _ j hv]
 have b:=m3w L g _ (L.sub_mem hR f) λj=> by simp[z0 u _ j d,z0 v _ j hv]
 fin_cases c<;>fin_cases x<;>fin_cases z<;>simp at l m n k<;>
  simp +decide only[m3,PV,d9,um,Bm,Cf,U4,R5,W8,
   d,hv,R8,R9,Fin.isValue,Fin.reduceAdd]at m1 b ⊢ <;>
  first
  | exact⟨by linear_combination (m1- b)/4,by linear_combination (m1+ b)/4⟩
  | exact⟨by linear_combination (m1- b)/8,by linear_combination (m1+ b)/8⟩
  | exact⟨by linear_combination (b- m1)/4,by linear_combination (m1+ b)/4⟩
  | exact⟨by linear_combination (b- m1)/8,by linear_combination (m1+ b)/8⟩
def Qm (u:Fq->ℂ) (a:u 0=0) (b:u≠0):u 1≠0\/u 2≠0\/u 3≠0:=by
 by_contra h;push_neg at h;apply b;funext i;fin_cases i<;>simp[a,h.1,h.2.1,h.2.2]
def bne (c:Fq):Bm (0,c)≠0:=by unfold Bm;split_ifs<;>norm_num
set_option maxHeartbeats 0 in
def r2k (L:Sq) (j:K5 L) (c x z:Fq) (m:c.val<2) (n:x≠c)
  (o:z≠c) (q:x≠z) (a d:ℂ) (y:a≠0) (A:d≠0) (ns:Bm (0,x)*a+ Bm (0,z)*d≠0)
  (u v:Fq->ℂ) (Ld:u 0=0) (f:v 0=0) (B:u≠0) (hv:v≠0)
  (s:d9 u (um (a*Bm (0,c)) (Bm (0,x)*a+ Bm (0,z)*d) c x)∈L)
  (dm:d9 v (um (d*Bm (0,c)) (Bm (0,x)*a+ Bm (0,z)*d) c z)∈L):
  c=0/\u x=0/\u z=0/\v x=0/\v z=0/\a=d:=by
 obtain⟨b,t⟩:=RI c x m n u Ld _ _ (λr=> j _ (L.smul_mem r s))
 obtain⟨q2,w⟩:=RI c z m o v f _ _ (λr=> j _ (L.smul_mem r dm))
 obtain⟨h,i⟩:=aa2 L j c x z m n o q u v Ld f _ _ _ _ s dm;have p:=j _ (L.add_mem s dm);have l:=bne c
 replace b:Qq c x u=0:=by simpa[y,l,ns] using b
 replace q2:Qq c z v=0:=by simpa[A,l,ns] using q2
 replace h:Cf u v=0:=by simpa[y,l,ns] using h
 replace i:Cf v u=0:=by simpa[A,l,ns] using i
 have e:Bm (0,c)*Mf u c*Mf v c- Bm (0,x)*Mf u x*Mf v c- Bm (0,z)*Mf v z*Mf u c=0:=by
  have :(Bm (0,x)*a+ Bm (0,z)*d)*(Bm (0,c)*Mf u c*Mf v c- Bm (0,x)*Mf u x*Mf v c-
    Bm (0,z)*Mf v z*Mf u c)=0:=by
   grind
  exact (Q3.1 this).resolve_left ns
 have C:=Qm u Ld B;have D:=Qm v f hv;have G:=cz _ _ _ (u 1) (u 2) (u 3) (LK 3 _ _) (LK 2 _ _) (LK 1 _ _) b;have K:=cz _ _ _ (v 1) (v 2) (v 3) (LK 3 _ _) (LK 2 _ _) (LK 1 _ _) q2;fin_cases c<;>simp at m
 .fin_cases x<;>fin_cases z<;>simp at n o q<;>
  simp +decide only[Qq,Cf,Mf,MU,pB,cr,um,d9,p4,Bm,R5,R8,
   R9,Fin.isValue,Ld,f]at b q2 h i e p t w ⊢ <;>
  rcases G with g | g | g | g<;>rcases K with k | k | k | k<;>grind
 .clear p t w;fin_cases x<;>fin_cases z<;>simp at n o q<;>
  simp +decide only[Qq,Cf,Mf,MU,pB,cr,Bm,R8,R9,Fin.isValue]at b q2 h i e ⊢ <;>
  rcases G with g | g | g | g<;>rcases K with k | k | k | k<;>grind
def r1k (L:Sq) (hL:K5 L) (c:Fq) (d:c.val<2) (h:Fq->ℂ)
  (hn:∀ x,x≠c->h x≠0) (a: ∑ j,Bm (0,j)*h j≠0) (t:h c=0)
  (i:∀ x,x≠c-> ∃ u:Fq->ℂ,u 0=0/\u≠0/\d9 u (um (h x*Bm (0,c)) (∑ j,Bm (0,j)*h j) c x)∈L):
  False:=by
 have f:(if c=0 then 1 else 0:Fq)≠c:=by fin_cases c<;>simp_all
 have l:(2:Fq)≠c:=by fin_cases c<;>simp_all
 have n:(3:Fq)≠c:=by fin_cases c<;>simp_all
 have F:(if c=0 then 1 else 0:Fq)≠2:=by split_ifs<;>decide
 have d13:(if c=0 then 1 else 0:Fq)≠3:=by split_ifs<;>decide
 obtain⟨u,s,Q,o⟩:=i _ f;obtain⟨v,D,hv,B⟩:=i _ l;obtain⟨w,E,R,adL⟩:=i _ n
 obtain⟨p,H⟩:=RI c _ d f u s _ _ (λr=> hL _ (L.smul_mem r o))
 obtain⟨q,J⟩:=RI c _ d l v D _ _ (λr=> hL _ (L.smul_mem r B))
 obtain⟨q3,M⟩:=RI c _ d n w E _ _ (λr=> hL _ (L.smul_mem r adL))
 obtain⟨c1,y⟩:=aa2 L hL c _ _ d f l F u v s D _ _ _ _ o B;obtain⟨z,A⟩:=aa2 L hL c _ _ d f n d13 u w s E _ _ _ _ o adL;have b:=bne c;have C:=hn _ f;have O:=hn _ l;have P:=hn _ n
 replace p:Qq c (if c=0 then 1 else 0) u=0:=by simpa[C,b,a] using p
 replace q:Qq c 2 v=0:=by simpa[O,b,a] using q
 replace q3:Qq c 3 w=0:=by simpa[P,b,a] using q3
 replace c1:Cf u v=0:=by simpa[C,b,a] using c1
 replace y:Cf v u=0:=by simpa[O,b,a] using y
 replace z:Cf u w=0:=by simpa[C,b,a] using z
 replace A:Cf w u=0:=by simpa[P,b,a] using A
 have S:=Qm u s Q;have T:=Qm v D hv;have U:=Qm w E R;have N: ∑ j,Bm (0,j)*h j=Bm (0,if c=0 then 1 else 0)*h (if c=0 then 1 else 0)+ Bm (0,2)*h 2+
   Bm (0,3)*h 3:=by
  fin_cases c<;>simp at d t ⊢ <;>simp[U4,t,Bm]<;>ring
 have e:Bm (0,c)*Mf u c*Mf v c*Mf w c- Bm (0,if c=0 then 1 else 0)*Mf u (if c=0 then 1 else 0)*
   Mf v c*Mf w c- Bm (0,2)*Mf v 2*Mf u c*Mf w c- Bm (0,3)*Mf w 3*Mf u c*Mf v c=0:=by
  have :(∑ j,Bm (0,j)*h j)*(Bm (0,c)*Mf u c*Mf v c*Mf w c- Bm (0,if c=0 then 1 else 0)*
    Mf u (if c=0 then 1 else 0)*Mf v c*Mf w c- Bm (0,2)*Mf v 2*Mf u c*Mf w c-
    Bm (0,3)*Mf w 3*Mf u c*Mf v c)=0:=by
   rw[N]at H J M ⊢;grind
  exact (Q3.1 this).resolve_left a
 clear H J M o B adL i N;have G:=cz _ _ _ (u 1) (u 2) (u 3) (LK 3 _ _) (LK 2 _ _) (LK 1 _ _) p;have K:=cz _ _ _ (v 1) (v 2) (v 3) (LK 3 _ _) (LK 2 _ _) (LK 1 _ _) q;have W:=cz _ _ _ (w 1) (w 2) (w 3) (LK 3 _ _) (LK 2 _ _) (LK 1 _ _) q3;fin_cases c<;>simp at d<;>
 simp +decide only[Qq,Cf,Mf,MU,pB,cr,Bm,R8,R9,Fin.isValue]at p q q3 c1 y z A e<;>
 rcases G with g | g | g | g<;>rcases K with k | k | k | k<;>rcases W with m | m | m | m<;>grind
def agS (L:Sq) (c:Fq): Prop :=
 (∃ x,x≠c/\(∀ X∈L,X (0,x)=0)/\ ∃ u:Fq->ℂ,u 0=0/\u≠0/\
   d9 u (um (Bm (0,c)) (Bm (0,x)) c x)∈L)\/
 (c=0/\ ∃ x z j:Fq,x≠0/\z≠0/\j≠0/\x≠z/\j≠x/\j≠z/\(∀ X∈L,X (0,x)+ X (0,z)=0)/\
   d9 (single j 1) (um 1 1 0 x)∈L)\/
 (∃ u:Fq->ℂ,u 0=0/\u≠0/\d9 u (single c 1)∈L/\ ∃ X∈L,∀ j,j≠c->X (0,j)=Bm (0,j))
lemma So (c x:Fq) (b:c.val<2) (a:x≠c) (p q f:Fq->ℂ):
  ∑ j,hv p q c j*f j=hv p q c x*f x+ hv p q c (cr c x 0)*f (cr c x 0)+
   hv p q c (cr c x 1)*f (cr c x 1):=by
 fin_cases c<;>fin_cases x<;>simp at b a<;>simp[U4,cr,hv]<;>ring
def aaH (c x:Fq) (a:x≠c):cr c x 0≠cr c x 1:=by
 fin_cases c<;>fin_cases x<;>simp at a<;>decide
def afH (L:Sq) (c x z j:Fq) (G:c.val<2) (KV:x≠c) (n:z≠c) (b:j≠c)
  (r:x≠z) (g:j≠x) (d:j≠z) (p q u v:Fq->ℂ) (C:u 0=0) (K:v 0=0) (y:u≠0) (E:v≠0)
  (l:hv p q c x≠0) (J:hv p q c z≠0) (H:Bm (0,x)*hv p q c x+ Bm (0,z)*hv p q c z≠0)
  (w:hv p q c j=0)
  (k:c=0/\u x=0/\u z=0/\v x=0/\v z=0/\hv p q c x=hv p q c z)
  (h:d9 u (um (hv p q c x*Bm (0,c)) (Bm (0,x)*hv p q c x+ Bm (0,z)*hv p q c z) c x)∈L)
  (s:∀ X∈L,∑ m,hv p q c m*X (0,m)=0)
  (hsp:∀ f:Fq->ℂ,∑ m,hv p q c m*f m=hv p q c x*f x+ hv p q c j*f j+ hv p q c z*f z)
  (a:∀ i,i=c\/i=x\/i=z\/i=j):agS L c:=by
 obtain⟨rfl,A,B,-,-,o⟩:=k
 have D:u j≠0:=λF=> y (funext λi=> by rcases a i with rfl | rfl | rfl | rfl<;>assumption)
 right;left
 refine⟨rfl,x,z,j,KV,n,b,r,g,d,λX t=> ?_,?_⟩
 .have e:=s X t;rw[hsp,w,<- o]at e
  have :hv p q 0 x*(X (0,x)+ X (0,z))=0:=by grind
  exact (Q3.1 this).resolve_left l
 .have e:d9 u (um (hv p q 0 x*Bm (0,0)) (Bm (0,x)*hv p q 0 x+ Bm (0,z)*hv p q 0 z) 0 x)=
    (2*hv p q 0 x*u j)•d9 (single j 1) (um 1 1 0 x):=by
   funext ⟨i,m⟩;rcases a i with rfl | rfl | rfl | rfl
   .simp[d9,C,b.symm]
   .simp[d9,A,g.symm]
   .simp[d9,B,d.symm]
   .simp only[d9,um,Q4,if_true,Q6,Q5,Bm,<- o,KV];split_ifs<;>simp_all<;>ring
  rw[e]at h;exact (L.smul_mem_iff (by simp[l,D])).1 h
def ajA (L:Sq) (t:K5 L) (T:finrank ℂ L=6) (c:Fq) (d:c.val<2)
  (S:finrank ℂ (L.map (af 0))=2) (K:∀ X∈L,X (0,c)=0):agS L c:=by
 have M:finrank ℂ ↥(Ar L 0)=4:=by have :=dx L (af 0);unfold Ar;omega
 obtain⟨D,N,E,O,J,x,hx⟩:=aei L c d S K;have s:=aje L t M c d K D E N O;set p:=r0 D;set q:=r0 E
 have V5:∀ X∈L,∑ j,hv p q c j*X (0,j)=0:=λX hX=> by
  obtain⟨a,b,G⟩:=J X hX;exact agd c d p q _ a b G
 have KV:x≠c:=by intro e;apply hx;simp[hv,e]
 obtain⟨z,A,B,C⟩:=acX c x KV;have Q:=bne c
 have H:=So c x d KV p q (λj=> Bm (0,j))
 obtain⟨⟨W,P,F⟩,u,l,hu,g⟩:=s x hx;by_cases h:sg p q c=0
 .right;right
  refine⟨u,l,hu,?_,(-(hv p q c x)⁻¹)•W,L.smul_mem _ P,λj R=> ?_⟩
  .have e:d9 u (um (hv p q c x*Bm (0,c)) (sg p q c) c x)=(hv p q c x*Bm (0,c))•d9 u (single c 1):=by
    funext ⟨i,j⟩;simp only[d9,um,h,Q4,Q6,Q5];split_ifs<;>ring
   rw[e]at g;exact (L.smul_mem_iff (mul_ne_zero hx Q)).1 g
  .simp only[Q6,Q5,F j R,h,ite_self];rw[zero_sub,mul_neg,neg_mul,neg_neg,<- X8,V9 hx,one_mul]
 have o:sg p q c=Bm (0,x)*hv p q c x+ Bm (0,cr c x 0)*hv p q c (cr c x 0)+
   Bm (0,cr c x 1)*hv p q c (cr c x 1):=by
  rw[show sg p q c= ∑ j,hv p q c j*Bm (0,j) by simp[sg,Az],H];ring
 by_cases hy:hv p q c (cr c x 0)=0<;>by_cases X6:hv p q c (cr c x 1)=0
 .left
  refine⟨x,KV,λX hX=> ?_,u,l,hu,?_⟩
  .have k:=V5 X hX;rw[So c x d KV,hy,X6]at k;simpa[hx] using k
  .have e:d9 u (um (hv p q c x*Bm (0,c)) (sg p q c) c x)=hv p q c x•d9 u (um (Bm (0,c)) (Bm (0,x)) c x):=by
    funext ⟨i,j⟩;rw[o,hy,X6];simp only[d9,um,Q6,Q5];split_ifs<;>ring
   rw[e]at g;exact (L.smul_mem_iff hx).1 g
 .obtain⟨-,v,r,m,n⟩:=s _ X6;rw[o,hy,T6,S0]at g n h;exact afH L c x (cr c x 1) (cr c x 0) d KV A z C.symm B (aaH c x KV) p q u v l r hu m hx X6
   h hy (r2k L t c x _ d KV A C.symm _ _ hx X6 h u v l r hu m g n) g V5
   (λf=>(So c x d KV p q f).trans (by ring)) λi=> by have :=Pq c x i KV;tauto
 .obtain⟨-,v,r,m,n⟩:=s _ hy;rw[o,X6,T6,S0]at g n h;exact afH L c x (cr c x 0) (cr c x 1) d KV z A B.symm C (aaH c x KV).symm p q u v l r hu m hx hy
   h X6 (r2k L t c x _ d KV z B.symm _ _ hx hy h u v l r hu m g n) g V5
   (λf=>(So c x d KV p q f).trans (by ring)) λi=> by have :=Pq c x i KV;tauto
 .exfalso
  have hn:∀ w,w≠c->hv p q c w≠0:=λw y=> by
   rcases Pq c x w KV with rfl | rfl | rfl | rfl
   .exact absurd rfl y
   .exact hx
   .exact hy
   .exact X6
  exact r1k L t c d (hv p q c) hn h (by simp[hv]) λw y=>(s w (hn w y)).2
def ig (c:Fq):Mt→ₗ[ℂ] Mt:=(gp (bn c)).comp Mv
lemma oq (c:Fq) (a:c.val<2):bn c 0=c/\bn c c=0/\(bn c).symm=bn c/\
  ∀ i,bn c (bn c i)=i:=by
 fin_cases c<;>simp at a<;>refine⟨by decide,by decide,?_,λi=> by fin_cases i<;>decide⟩<;>
  ext i<;>fin_cases i<;>decide
lemma Ip (c:Fq) (a:c.val<2) (X:Mt) (i j:Fq):ig c X (i,j)=X (bn c j,bn c i):=by
 simp[ig,my,Mw,(oq c a).2.2.1]
def R3 (c:Fq) (d:c.val<2) (L:Sq) (Y:Mt) (b:Y∈L.map (ig c)):
  ∃ X∈L,∀ i j,Y (i,j)=X (bn c j,bn c i):=by
 obtain⟨X,a,rfl⟩:=Af.1 b;exact⟨X,a,Ip c d X⟩
def aaN (c:Fq) (L:Sq) (a:K5 L):
  ∀ t∈L.map (ig c),p4 (Bm+ t)=65:=by
 rw[ig,Y4];exact LY _ (QR L a) _
lemma aaM (c:Fq) (L:Sq):finrank ℂ (L.map (ig c))=finrank ℂ L:=by
 rw[ig,Y4,o6,Qv]
lemma UG (c:Fq) (a:c.val<2) (L:Sq):
  finrank ℂ ((L.map (ig c)).map (af 0))=finrank ℂ (L.map (Kl c)):=by
 rw[ig,Y4,KW,(oq c a).2.2.1,(oq c a).1,<- Y4];rfl
lemma Nj (c:Fq) (a:c.val<2) (L:Sq):(L.map (ig c)).map (ig c)=L:=by
 rw[<- Y4];convert Submodule.map_id L;apply LinearMap.ext;intro X;funext ⟨i,j⟩;simp only[Al,Ba,Ip c a,(oq c a).2.2.2]
def R4 (c:Fq) (hc:c.val<2) (L:Sq) (u a:Fq->ℂ) (h:d9 u a∈L.map (ig c)):
  d9 (λi=> a (bn c i)) (λj=> u (bn c j))∈L:=by
 obtain⟨X,b,e⟩:=R3 c hc L _ h;convert b using 1;funext ⟨i,j⟩;have :=e (bn c j) (bn c i);simp only[d9,(oq c hc).2.2.2]at this ⊢;grind
def Zy (c x i:Fq): Prop :=c=0\/x=0\/(x=2/\i=3)\/(x=3/\i=2)
def kA (L:Sq) (o:K5 L) (c x i a:Fq) (e:ℂ) (hc:c.val<2) (b:x≠c)
  (g:i≠0) (p:(e=0/\i=a)\/(e=1/\c=0/\a≠i/\a≠0)) (m:e=1\/Zy c x i)
  (u:Fq->ℂ) (u0:u 0=0) (hu:u≠0) (d:d9 u (um (Bm (0,c)) (Bm (0,x)) c x)∈L)
  (l:∀ X∈L,X (i,c)+ e*X (a,c)=0):False:=by
 obtain⟨q,f⟩:=RI c x hc b u u0 _ _ (λr=> o _ (L.smul_mem r d))
 have k:=l _ d;have s:=Qm u u0 hu;simp only[d9,um,if_true]at k;rcases p with⟨rfl,rfl⟩ | ⟨rfl,n,j,h⟩
 .fin_cases c<;>simp at hc<;>fin_cases x<;>simp at b<;>fin_cases i<;>simp at g<;>simp[Zy]at m<;>
  simp +decide only[Qq,Mf,MU,pB,cr,Bm,R8,R9,Fin.isValue]at q f k ⊢ <;>
  grind
 .subst n;fin_cases x<;>simp at b<;>fin_cases i<;>simp at g<;>fin_cases a<;>simp at h j<;>
  simp +decide only[Qq,Mf,MU,pB,cr,Bm,R8,R9,Fin.isValue]at q f k ⊢ <;>
  grind
def kP (L:Sq) (a:K5 L) (c x:Fq) (m:c.val<2) (p:x≠c)
  (f:c=0\/x=0) (u w:Fq->ℂ) (e:u 0=0) (n:u≠0) (r:w c=0) (s:w x=0) (o:w≠0)
  (b:d9 u (um (Bm (0,c)) (Bm (0,x)) c x)∈L) (d:d9 (single 0 1) w∈L):False:=by
 have g:=a _ b;have i:=a _ (L.neg_mem b);have e3:=a _ d;have k:=a _ (L.add_mem b d);have l:=a _ (L.add_mem (L.neg_mem b) d);have t:=Qm u e n
 have q:w 0≠0\/w 1≠0\/w 2≠0\/w 3≠0:=by
  by_contra h;push_neg at h;apply o;funext j;fin_cases j<;>simp[h.1,h.2.1,h.2.2.1,h.2.2.2]
 fin_cases c<;>simp at m<;>fin_cases x<;>simp at p f<;>
  simp +decide only[p4,d9,um,Bm,R5,Aa,Q4,e,
   R8,R9,Fin.isValue,r,s]at g i e3 k l q ⊢ <;>
  grind
def aoX (L:Sq) (a:K5 L) (x:Fq) (s:x=2\/x=3) (u d:Fq->ℂ)
  (f:u 0=0) (e:d 0=0) (r:u≠0) (g:d≠0) (Sj:∀ X∈L,X (0,x)=0)
  (h:∀ X∈L,X (bn 1 x,1)=0) (c:d9 u (um (Bm (0,1)) (Bm (0,x)) 1 x)∈L)
  (b:d9 (λi=> um (Bm (0,1)) (Bm (0,x)) 1 x (bn 1 i)) (λj=> d (bn 1 j))∈L):False:=by
 have t:=h _ c;have v:=Sj _ b;have e1:=a _ c;have k:=a _ (L.neg_mem c);have l:=a _ b;have m:=a _ (L.neg_mem b);have n:=a _ (L.add_mem c b);have o:=a _ (L.sub_mem c b);have p:=a _ (L.add_mem (L.neg_mem c) b);have q:=a _ (L.sub_mem (L.neg_mem c) b);have w:=Qm u f r;have y:=Qm d e g;rcases s with rfl | rfl<;>
  simp +decide only[p4,d9,um,Bm,bn,T0,R5,W8,
   Aa,f,e,R8,R9,Fin.isValue]at t v e1 k l m n o p q w y ⊢ <;>
  grind
def kDD (L:Sq) (c:K5 L) (j x a:Fq) (l:j≠0) (m:x≠0)
  (h:a≠0) (i:j≠x) (k:j≠a) (g:d9 (single j 1) (um 1 1 0 x)∈L)
  (b:d9 (um 1 1 0 a) (single j 1)∈L):False:=by
 have d:=c _ g;have e:=c _ b;have f:=c _ (L.add_mem g b);fin_cases j<;>fin_cases x<;>fin_cases a<;>simp at l m h i k<;>
  simp +decide [p4,d9,um,Bm,Q4]at d e f<;>norm_num at d e f
def kDS (L:Sq) (a:K5 L) (j x z:Fq) (m:j≠0) (o:x≠0) (p:z≠0)
  (h:j≠x) (e:j≠z) (g:x≠z) (w:Fq->ℂ) (f:w 0=0) (b:w x+ w z=0) (n:w≠0)
  (c:d9 (single j 1) (um 1 1 0 x)∈L) (d:d9 (single 0 1) w∈L):False:=by
 have i:=a _ d;have k:=a _ (L.add_mem c d);have l:=a _ c;have q:w 1≠0\/w 2≠0\/w 3≠0:=Qm w f n;fin_cases j<;>fin_cases x<;>fin_cases z<;>simp at m o p h e g<;>
  simp +decide only[p4,d9,um,Bm,R5,Q4,f,R8,R9,
   Fin.isValue]at i k l b q ⊢ <;>
  grind
def acS {V: Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (β:V→ₗ[ℂ] Module.Dual ℂ V) (f:∀ x y,β x y= β y x) (W:Submodule ℂ V)
  (c:∀ x∈W,∀ y∈W,β x y=0):
  2*finrank ℂ W+ finrank ℂ (ker β)≤
   finrank ℂ V+2*finrank ℂ ↥(W ⊓ ker β):=by
 have b:W.map β≤(W ⊔ ker β).dualAnnihilator:=by
  rintro _ ⟨x,g,rfl⟩;rw[Submodule.mem_dualAnnihilator];intro y h;obtain⟨a,d,r,e,rfl⟩:=V0.1 h;rw[S4,c x g a d,f x r,Am.1 e];simp
 have i:=Cu (W ⊔ ker β);have j:=W1 b;have k:=dx W β;have l:=Bb W (ker β);omega
def bf (z w:Ft->ℂ) (M N:B9):ℂ:=
 ∑ a:Ft,∑ b:Ft,∑ c:Ft,∑ d:Ft,j1 z a c*j1 w b d*M (a,b)*N (c,d)
def bfL (z w:Ft->ℂ):B9→ₗ[ℂ] Module.Dual ℂ B9:=
 LinearMap.mk₂ ℂ (bf z w)
  (λM a N=> by simp only[bf,R1,R5];ring)
  (λc M N=> by simp only[bf,R1,Q6,Q5];ring)
  (λM N b=> by simp only[bf,R1,R5];ring)
  (λc M N=> by simp only[bf,R1,Q6,Q5];ring)
lemma XG (z w:Ft->ℂ) (M N:B9):bfL z w M N=bf z w M N:=rfl
def af7 (z w:Ft->ℂ) (M N:B9):bf z w M N=bf z w N M:=by
 simp only[bf,j1,ah,R1];simp;ring
lemma adu (z w:Ft->ℂ) (M N:B9):
  bf z w M N=Qf z w (M+ N)- Qf z w M- Qf z w N:=by
 simp only[bf,Qf,j1,ah,R1,R5];simp;ring
lemma acj (z w:Ft->ℂ) (M:B9) (c d:Ft):
  bf z w M (λq=> if q=(c,d) then 1 else 0)=
   ∑ a:Ft,∑ b:Ft,j1 z a c*j1 w b d*M (a,b):=by
 simp only[bf]
 refine Bp rfl λa _=> Bp rfl λb _=> ?_
 rw[Cw c,Cw d]
 .simp
 .intro e _ g;simp[g]
 .simp
 .intro h _ f
  refine Finset.sum_eq_zero λe _=> ?_
  simp[f]
 .simp
lemma agX (z w:Ft->ℂ) (g:z 0*z 1*z 2≠0) (f:w 0*w 1*w 2≠0):
  ker (bfL z w)= ⊥ :=by
 rw[Cv];intro M e
 have h:∀ c d:Ft,∑ a:Ft,∑ b:Ft,j1 z a c*j1 w b d*M (a,b)=0:=by
  intro c d;rw[<- acj,<- XG,e];rfl
 have od:4*(z 0*z 1*z 2)*(w 0*w 1*w 2)≠0:=
  mul_ne_zero (mul_ne_zero (by norm_num) g) f
 funext ⟨a,b⟩;have k:4*(z 0*z 1*z 2)*(w 0*w 1*w 2)*M (a,b)= ∑ c:Ft,∑ d:Ft,(2*(if a=c then 1 else 0)-1)*z a*z c*
   ((2*(if b=d then 1 else 0)-1)*w b*w d)* ∑ i:Ft,∑ j:Ft,j1 z i c*j1 w j d*M (i,j):=by
  fin_cases a<;>fin_cases b<;>simp[j1,R1]<;>ring
 simp only[h,T6,Finset.sum_const_zero]at k;simpa[od] using k
def acR (z w:Ft->ℂ) (e:z 0*z 1*z 2≠0) (d:w 0*w 1*w 2≠0)
  (W:Submodule ℂ B9) (a:∀ M∈W,Qf z w M=0):finrank ℂ W≤4:=by
 have i:=acS (bfL z w) (λx y=> af7 z w x y) W (λx b y c=> by
  rw[XG,adu,a _ (W.add_mem b c),a x b,a y c];ring)
 have f:finrank ℂ ↥(ker (bfL z w))=0:=by rw[agX z w e d];simp
 have g:finrank ℂ ↥(W ⊓ ker (bfL z w))≤ finrank ℂ ↥(ker (bfL z w)):=
  W1 By
 have h:finrank ℂ B9=9:=by simp[B9]
 omega
def bx (c:Fq) (a:c.val<2) (Y:Mt) (u:Fq->ℂ) (b:u 0=0):
  p4 (Y+ d9 u (single c 1))- p4 Y=
   Qf (λi=> u (rR i)) (λj=> Y (0,bn c (rR j))) (dq c Y):=by
 fin_cases c<;>simp at a<;>
  simp[p4,d9,Qf,ah,rR,dq,bn,R1,b,Q4,T0]<;>ring
lemma aeg (z w:Ft->ℂ) (A T:B9) (a:ℂ):
  Qf z w (A+ a•T)=Qf z w A+ a*(Qf z w (A+ T)- Qf z w A- Qf z w T)+ a^2*Qf z w T:=by
 simp only[Qf,R1,R5,Q6,Q5];ring
lemma ajz (z v v':Ft->ℂ) (a b:ℂ) (M:B9):
  Qf z (λj=> a*v j+ b*v' j) M=a*Qf z v M+ b*Qf z v' M:=by
 simp only[Qf,R1];ring
lemma sg3 (c:Fq) (a:c.val<2) (j:Ft):bn c (rR j)≠c/\rR j≠0:=by
 fin_cases c<;>simp at a<;>fin_cases j<;>simp[rR,bn,T0]
def ajB (P:Submodule ℂ (Fq->ℂ)) (e:finrank ℂ P=2) (v w f x:Fq->ℂ) (hv:v∈P) (n:w∈P)
  (c:x∈P) (hf: ∑ j,f j*v j≠0) (hfw: ∑ j,f j*w j=0) (d:w≠0):
  ∃ a b:ℂ,∀ j,x j=a*v j+ b*w j:=by
 have m:LinearIndependent ℂ ![v,w]:=by
  refine Cl.2 λa b h=> ?_
  have k:a* ∑ j,f j*v j=0:=by
   have :=congrArg (λy:Fq->ℂ=> ∑ j,f j*y j) h
   simp only[U4,R5,Q6,Q5,W0]at this hfw ⊢;grind
  have ha:a=0:=(Q3.1 k).resolve_right hf;subst ha;rw[T9,Y0,smul_eq_zero]at h;exact⟨rfl,h.resolve_right d⟩
 have he:span ℂ (Set.range ![v,w])=P:=
  Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (Cx.2 λi=> by fin_cases i<;>simpa))
   (by rw[Bq m,e];simp)
 rw[<- he,An]at c;obtain⟨g,l⟩:=c
 exact⟨g 0,g 1,λj=> by rw[<- l];simp[Ag]⟩
def apl (c:Fq) (k:c.val<2) (Y:Mt) (h:dq c Y=0):p4 Y=0:=by
 have e:∀ i j,Y (rR i,bn c (rR j))=0:=λi j=> congrFun h (i,j)
 have YI:=e 0 0;have TX:=e 0 1;have Qo:=e 0 2;have a:=e 1 0;have b:=e 1 1;have b12:=e 1 2;have d:=e 2 0;have f:=e 2 1;have g:=e 2 2;rcases I7 c k with rfl | rfl<;>simp[rR,bn,T0]at YI TX Qo a b b12 d f g<;>
  simp[p4,YI,TX,Qo,a,b,b12,d,f,g]
lemma kB (L:Sq) (e:K5 L) (c:Fq) (f:c.val<2):
  L.map (dq c) ⊓ span ℂ {dq c Bm}= ⊥ :=by
 rw[Cj];intro x h;obtain⟨hx1,d⟩:=U1.1 h;obtain⟨t,g,rfl⟩:=Af.1 hx1;obtain⟨l,b⟩:=X3.1 d;rw[Av];by_cases a:l=0
 .rw[<- b,a,T9]
 exfalso
 have k:=apl c f (Bm+ -(l⁻¹•t)) (by
  rw[S4,map_neg,S5,<- b,Ae,V9 a,Aw,add_neg_cancel])
 rw[e _ (L.neg_mem (L.smul_mem _ g))]at k;norm_num at k
lemma kzr (c:Fq) (y:c.val<2) (K:Mt) (u w:Fq->ℂ) (B:u 0=0) (C:w c=0) (a b a' d:ℂ)
  (o:∀ j,j≠c->K (0,j)=a*Bm (0,j)+ b*w j) (p:∀ i,i≠0->K (i,c)=a'*Bm (i,c)+ d*u i)
  (z:K (0,c)=0) (eb:∀ i j,K (rR i,bn c (rR j))=0) (q:p4 (Bm+ K)=65) (r:p4 (Bm+ -K)=65)
  (s:p4 (Bm+ d9 u (single c 1))=65) (t:p4 (Bm+ d9 (single 0 1) w)=65)
  (v:p4 (Bm+(d9 u (single c 1)+ d9 (single 0 1) w))=65):a=0/\a'=0:=by
 have m:=eb 0 0;have l:=eb 0 1;have k:=eb 0 2;have e:=eb 1 0;have f:=eb 1 1;have g:=eb 1 2;have h:=eb 2 0;have b21:=eb 2 1;have b22:=eb 2 2;rcases I7 c y with rfl | rfl<;>simp[rR,bn,T0]at m l k e f g h b21 b22<;>
  simp +decide only[p4,d9,Bm,R5,Aa,Q4,B,C,z,
   m,l,k,e,f,g,h,b21,b22,o,p,ne_eq,R8,R9,Fin.isValue,
   not_false_eq_true]at q r s t v
 all_goals
  have A:a+ a'=0:=by
   first
   | grind
   | grind
  have D:a*a'=0:=by
   first
   | grind
   | grind
  have x:a^2=0:=by grind
  have n:a=0:=pow_eq_zero_iff two_ne_zero |>.1 x
  exact⟨n,by linear_combination A- n⟩
def apd (L:Sq) (hL:K5 L) (c:Fq) (f:c.val<2)
  (C:∀ X∈L,X (0,c)=0) (u w:Fq->ℂ) (v:u 0=0) (D:w c=0)
  (hS:d9 u (single c 1)∈L) (p:d9 (single 0 1) w∈L)
  (q r:Mt) (x:∀ j,j≠c->q (0,j)=Bm (0,j)) (y:∀ i,i≠0->r (i,c)=Bm (i,c))
  (B:∀ t∈L,∃ a b:ℂ,∀ j,t (0,j)=a*q (0,j)+ b*w j)
  (A:∀ t∈L,∃ a d:ℂ,∀ i,t (i,c)=a*r (i,c)+ d*u i):
  L ⊓ ker (dq c)≤ span ℂ (Set.range ![d9 u (single c 1),d9 (single 0 1) w]):=by
 intro K m;obtain⟨QK,h⟩:=U1.1 m;rw[Am]at h;obtain⟨a,b,k⟩:=B K QK;obtain⟨z,d,l⟩:=A K QK
 have s:∀ i j,K (rR i,bn c (rR j))=0:=λi j=> congrFun h (i,j)
 obtain⟨rfl,rfl⟩:=kzr c f K u w v D a b z d (λj g=> by rw[k,x j g])
  (λi e=> by rw[l,y i e]) (C K QK) s (hL _ QK) (hL _ (L.neg_mem QK)) (hL _ hS) (hL _ p)
  (hL _ (L.add_mem hS p))
 have m:K=d•d9 u (single c 1)+ b•d9 (single 0 1) w:=by
  funext ⟨i,j⟩;simp only[R5,Q6,Q5,d9,Q4];by_cases e:i=0
  .rw[e,k];simp[v]
  by_cases g:j=c
  .rw[g,l];simp[e]
  obtain⟨n,rfl⟩:∃ n,i=rR n:=by
   fin_cases i<;>simp at e<;>first | exact⟨0,by decide⟩ | exact⟨1,by decide⟩ | exact⟨2,by decide⟩
  obtain⟨o,rfl⟩:∃ o,j=bn c (rR o):=by
   rcases I7 c f with rfl | rfl<;>fin_cases j<;>simp at g<;>
    first | exact⟨0,by decide⟩ | exact⟨1,by decide⟩ | exact⟨2,by decide⟩
  rw[s];simp[(sg3 c f o).1,(sg3 c f n).2]
 rw[m];exact V7 _ (T4 _ _ (Cy ⟨0,rfl⟩))
  (T4 _ _ (Cy ⟨1,rfl⟩))
def ape (L:Sq) (e:K5 L) (c:Fq) (f:c.val<2) (u w:Fq->ℂ)
  (p:u 0=0) (o:d9 u (single c 1)∈L) (h:d9 (single 0 1) w∈L)
  (k:Mt) (QM:∀ j,j≠c->k (0,j)=Bm (0,j))
  (r:∀ t∈L,∃ a b:ℂ,∀ j,t (0,j)=a*k (0,j)+ b*w j):
  ∀ M∈L.map (dq c) ⊔ span ℂ {dq c Bm},
   Qf (λi=> u (rR i)) (λj=> Bm (0,bn c (rR j))) M=0:=by
 have bS':dq c (d9 (single 0 1) w)=0:=by
  funext ⟨i,j⟩;fin_cases i<;>simp[dq,d9,rR]
 intro M A;obtain⟨y,B,z,q,rfl⟩:=V0.1 A;obtain⟨t,d,rfl⟩:=Af.1 B;obtain⟨l,rfl⟩:=X3.1 q;obtain⟨a,b,g⟩:=r t d
 have G:∀ τ:ℂ,(1+ τ*a)*Qf (λi=> u (rR i)) (λj=> Bm (0,bn c (rR j)))
   (dq c Bm+ τ•dq c t)=0:=λτ=> by
  have m:=bx c f (Bm+ τ•t) u p;have n:=bx c f (Bm+ τ•t+ d9 (single 0 1) w) u p;have E:p4 (Bm+ τ•t)=65:=e _ (L.smul_mem τ d)
  have F:p4 (Bm+ τ•t+ d9 u (single c 1))=65:=by
   rw[Bs];exact e _ (L.add_mem (L.smul_mem τ d) o)
  have H:p4 (Bm+ τ•t+ d9 (single 0 1) w)=65:=by
   rw[Bs];exact e _ (L.add_mem (L.smul_mem τ d) h)
  have J:p4 (Bm+ τ•t+ d9 (single 0 1) w+ d9 u (single c 1))=65:=by
   rw[Bs,Bs];exact e _ (L.add_mem (L.smul_mem τ d) (L.add_mem h o))
  rw[F,E]at m;rw[J,H]at n
  have C:(λj=>(Bm+ τ•t) (0,bn c (rR j)))=λj=>
    (1+ τ*a)*Bm (0,bn c (rR j))+(τ*b)*w (bn c (rR j)):=funext λj=> by
   simp only[R5,Q6,Q5];rw[g,QM _ (sg3 c f j).1];ring
  have D:(λj=>(Bm+ τ•t+ d9 (single 0 1) w) (0,bn c (rR j)))=λj=>
    (1+ τ*a)*Bm (0,bn c (rR j))+(τ*b+1)*w (bn c (rR j)):=funext λj=> by
   simp only[R5,Q6,Q5,d9,Pi.single_eq_same];rw[g,QM _ (sg3 c f j).1];ring
  rw[C,ajz,S4,S5]at m;rw[D,ajz,S4,S4,S5,bS',S0]at n;grind
 have s:=G 0;have v:=G 1;have gm:=G (-1);have x:=G 2;rw[aeg]at s v gm x;rw[aeg,Bo (dq c t) (dq c Bm)];grind
def krh (L:Sq) (g:K5 L) (N:finrank ℂ L=6) (c:Fq) (hc:c.val<2)
  (E:finrank ℂ (L.map (af 0))=2) (G:finrank ℂ (L.map (Kl c))=2) (r:∀ X∈L,X (0,c)=0)
  (u w:Fq->ℂ) (l:u 0=0) (s:w c=0) (J:w≠0)
  (k:d9 u (single c 1)∈L) (Oc:d9 (single 0 1) w∈L)
  (Xb:Mt) (m:Xb∈L) (p:∀ j,j≠c->Xb (0,j)=Bm (0,j))
  (Xg:Mt) (n:Xg∈L) (v:∀ i,i≠0->Xg (i,c)=Bm (i,c)):u 1*u 2*u 3=0:=by
 by_contra o
 have H:u≠0:=λh=> o (by simp[h])
 have z:=r Xb m;have A:=r Xg n;have C:=g _ k;have D:=g _ Oc;have F:(∑ i,MU i c*u i=0/\ ∑ j,MU 0 j*w j=0)/\ ∑ j,MU 0 j*Xb (0,j)≠0/\
   ∑ i,MU i c*Xg (i,c)≠0:=by
  rcases I7 c hc with rfl | rfl<;>
   simp +decide only[p4,d9,Bm,R5,Q4,l,s,R8,
    R9,Fin.isValue]at C D<;>
   refine⟨⟨?_,?_⟩,?_,?_⟩<;>
   simp +decide only[U4,MU,Bm,l,s,z,A,p,v,ne_eq,
    not_false_eq_true,R8,R9,Fin.isValue]<;>
   first | grind
 have x:∀ t∈L,∃ a b:ℂ,∀ j,t (0,j)=a*Xb (0,j)+ b*w j:=λt q=> by
  obtain⟨a,b,e⟩:=ajB _ E (af 0 Xb) w (λj=> MU 0 j) (af 0 t) (S8 m)
   (by convert S8 (f:=af 0) Oc;funext j;simp[bu,d9])
   (S8 q) F.2.1 F.1.2 J
  exact⟨a,b,λj=> by simpa[bu] using e j⟩
 have B:∀ t∈L,∃ a d:ℂ,∀ i,t (i,c)=a*Xg (i,c)+ d*u i:=λt q=> by
  obtain⟨a,d,e⟩:=ajB _ G (Kl c Xg) u (λi=> MU i c) (Kl c t) (S8 n)
   (by convert S8 (f:=Kl c) k;funext i;simp[Nt,d9])
   (S8 q) F.2.2 F.1.1 H
  exact⟨a,d,λi=> by simpa[Nt] using e i⟩
 have M:=acR (λi=> u (rR i)) (λj=> Bm (0,bn c (rR j))) (by simpa[rR] using o)
  (by rcases I7 c hc with rfl | rfl<;>norm_num[Bm,rR,bn,T0]) _
  (ape L g c hc u w l k Oc Xb p x)
 have O:=dx L (dq c)
 have P:finrank ℂ ↥(L ⊓ ker (dq c))≤2:=by
  have :=finrank_range_le_card (R:= ℂ) (b:= ![d9 u (single c 1),d9 (single 0 1) w]);simp only[Bc]at this;exact (W1 (apd L g c hc r u w l s k Oc Xb Xg p v x B)).trans this
 have y:dq c Bm≠0:=λh=> by
  have :=congrFun h (0,0);rcases I7 c hc with rfl | rfl<;>simp[dq,rR,bn,Bm]at this
 have K:=Bb (L.map (dq c)) (span ℂ {dq c Bm});rw[kB L g c hc,V3,Ab y]at K;omega
def krf (L:Sq) (a:K5 L) (c:Fq) (k:c.val<2) (u w:Fq->ℂ)
  (f:u 0=0) (p:w c=0) (l:u≠0) (m:w≠0) (d:d9 u (single c 1)∈L)
  (b:d9 (single 0 1) w∈L) (n:u 1*u 2*u 3=0)
  (e:w (bn c 1)*w (bn c 2)*w (bn c 3)=0):False:=by
 have g:=a _ d;have i:=a _ b;have f3:=a _ (L.add_mem d b);have q:=Qm u f l
 have o:w 0≠0\/w 1≠0\/w 2≠0\/w 3≠0:=by
  by_contra h;push_neg at h;apply m;funext j;fin_cases j<;>simp[h.1,h.2.1,h.2.2.1,h.2.2.2]
 obtain h1 | h1 | h1:u 1=0\/u 2=0\/u 3=0:=by simpa[Q3,or_assoc] using n
 all_goals rcases I7 c k with rfl | rfl
 all_goals
  simp +decide only[p4,d9,Bm,R5,Q4,f,p,h1,bn,
   T0,Equiv.Perm.one_apply,R8,R9,Fin.isValue]at g i f3 e o
  obtain (h2 | h2) | h2:=(Q3.1 e).imp_left Q3.1
 all_goals grind
def E3p: Prop := ∀ L:Sq,K5 L->finrank ℂ L=6-> ∀ c:Fq,c.val<2->
 finrank ℂ (L.map (af 0))=2->finrank ℂ (L.map (Kl c))=2->(∀ X∈L,X (0,c)=0)->False
def abU: Prop := ∀ L:Sq,K5 L->finrank ℂ L=6->
 finrank ℂ (L.map (af 0))=2->finrank ℂ (L.map (Kl 1))=2->(∀ X∈L,X (0,1)=0)->
 ∀ x:Fq,(x=2\/x=3)->(∀ X∈L,X (0,x)=0)->
 ∀ u w:Fq->ℂ,u 0=0->u≠0->d9 u (um 1 1 1 x)∈L->w 1=0->w x=0->w≠0->
  d9 (single 0 1) w∈L->False
def WN (c:Fq) (a:c.val<2) (u:Fq->ℂ) (b:u≠0):(λj=> u (bn c j))≠0:=λh=>
 b (funext λj=> by have :=congrFun h (bn c j);simpa[(oq c a).2.2.2] using this)
lemma ssg (c:Fq) (a:c.val<2):(λi=>(single c (1:ℂ):Fq->ℂ) (bn c i))=single 0 1:=by
 funext i;fin_cases c<;>simp at a<;>fin_cases i<;>simp[bn,T0,Q4]
def ok3:∀ c x a:Fq,c.val<2->x≠c->a≠c-> ¬ Zy c x (bn c a)-> ¬ Zy c a (bn c x)->
  c=1/\x=a/\(x=2\/x=3):=by
 intro c x a;fin_cases c<;>fin_cases x<;>fin_cases a<;>simp[Zy,bn,T0]
def ok2:∀ c x:Fq,c.val<2->x≠c-> ¬ (c=0\/x=0)->c=1/\(x=2\/x=3):=by decide
def jj:∀ j x z a:Fq,j≠0->x≠0->z≠0->a≠0->x≠z->a≠x->a≠z->j≠x->j≠z->j=a:=by
 intro j x;fin_cases j<;>fin_cases x<;>decide
def afP (hH:abU):E3p:=by
 intro L hL P c hc Q hq R;obtain⟨B,p,ss,q⟩:=oq c hc;have s:=aaN c L hL
 have Lx:finrank ℂ (L.map (ig c))=6:=by rw[aaM];exact P
 have M:finrank ℂ ((L.map (ig c)).map (af 0))=2:=by rw[UG c hc];exact hq
 have OW:finrank ℂ ((L.map (ig c)).map (Kl c))=2:=by rw[<- UG c hc,Nj c hc];exact Q
 have KR:∀ Y∈L.map (ig c),Y (0,c)=0:=λY v=> by
  obtain⟨X,d,e⟩:=R3 c hc L Y v;rw[e,p,B];exact R X d
 have w:∀ X∈L,ig c X∈L.map (ig c):=λX d=> S8 d
 have J:∀ u a,ig c (d9 u a)=d9 (λi=> a (bn c i)) (λj=> u (bn c j)):=λu a=> by
  funext ⟨i,j⟩;simp[Ip c hc,d9];ring
 have ag:∀ i j,(∀ Y∈L.map (ig c),Y (i,j)=0)-> ∀ X∈L,X (bn c j,bn c i)=0:=λi j h X d=> by
  have :=h _ (w X d);rwa[Ip c hc]at this
 have ae:∀ i j,(∀ X∈L,X (i,j)=0)-> ∀ Y∈L.map (ig c),Y (bn c j,bn c i)=0:=λi j h Y v=> by
  obtain⟨X,d,e⟩:=R3 c hc L Y v;rw[e,q,q];exact h X d
 have XW:=ajA L hL P c hc Q R;have Ng:=ajA _ s Lx c hc M KR;rcases XW with⟨x,n,y,u,m,l,A⟩ | ⟨rfl,x,z,j,n,QO,hj,SZ,Wh,am,PH,hD⟩ |
   ⟨u,m,l,hS,Xb,hXb,QM⟩<;>
  rcases Ng with⟨b,RN,G,u',Re,g,dm⟩ | ⟨W,b,C,j',RN,E,Z,H,Zl,U,F,V⟩ |
   ⟨u',Re,g,Oc,Xg,hXg,Vj⟩
 .have o:=ag 0 b G;rw[B]at o
  have K:bn c b≠0:=λh=> RN (by rw[<- q b,h,B])
  by_cases ho:Zy c x (bn c b)
  .exact kA L hL c x _ _ 0 hc n K (Or.inl ⟨rfl,rfl⟩) (Or.inr ho) u m l A (λX d=> by simp[o X d])
  by_cases Zm:Zy c b (bn c x)
  .have S:=ae 0 x y;rw[B]at S
   have aj:bn c x≠0:=λh=> n (by rw[<- q x,h,B])
   exact kA _ s c b _ _ 0 hc RN aj (Or.inl ⟨rfl,rfl⟩) (Or.inr Zm) u' Re g dm (λY v=> by simp[S Y v])
  obtain⟨rfl,rfl,t⟩:=ok3 c x b hc n RN ho Zm;exact aoX L hL x t u u' m Re l g y o A (R4 1 hc L _ _ dm)
 .subst W
  have o:∀ X∈L,X (b,0)+1*X (C,0)=0:=λX d=> by
   have :=F _ (w X d);simpa[Ip 0 hc,bn] using this
  exact kA L hL 0 x b C 1 hc n RN (Or.inr ⟨rfl,rfl,H.symm,E⟩) (Or.inl rfl) u m l A o
 .have f:=R4 c hc L _ _ Oc;rw[ssg c hc]at f
  have O:u' (bn c x)=0:=by have :=y _ f;simpa[d9] using this
  have N:u' (bn c c)=0:=by rw[p];exact Re
  by_cases D:c=0\/x=0
  .exact kP L hL c x hc n D u _ m l N O (WN c hc u' g) A f
  obtain⟨rfl,t⟩:=ok2 c x hc n D
  have e:Bm (0,1)=1/\Bm (0,x)=1:=by rcases t with rfl | rfl<;>simp[Bm]
  rw[e.1,e.2]at A;exact hH L hL P Q hq R x t y u _ m l A N O (WN 1 hc u' g) f
 .have o:∀ Y∈L.map (ig 0),Y (x,0)+1*Y (z,0)=0:=λY v=> by
   obtain⟨X,d,e⟩:=R3 0 hc L Y v;have :=PH X d;simp[e,bn]at this ⊢;grind
  exact kA _ s 0 b x z 1 hc RN n (Or.inr ⟨rfl,rfl,SZ.symm,QO⟩) (Or.inl rfl) u' Re g dm o
 .have o:∀ X∈L,X (b,0)+ X (C,0)=0:=λX d=> by
   have :=F _ (w X d);simpa[Ip 0 hc,bn] using this
  have k:=o _ hD;simp[d9,um,Q4]at k
  have a1:j≠b:=by rintro rfl;simp at k;split_ifs at k<;>norm_num at k
  have a2:j≠C:=by rintro rfl;simp at k;split_ifs at k<;>norm_num at k
  have al:=jj j b C j' hj RN E Z H Zl U a1 a2;subst al;have T:=R4 0 hc L _ _ V;simp only[bn]at T
  exact kDD L hL j x b hj n RN Wh Zl hD (by simpa using T)
 .have f:=R4 0 hc L _ _ Oc;rw[ssg 0 hc]at f;have k:=PH _ f;simp[d9]at k
  exact kDS L hL j x z hj n QO Wh am SZ _ (by simpa[bn] using Re) k (WN 0 hc u' g) hD f
 .have r:d9 (single 0 1) (λj=> u (bn c j))∈L.map (ig c):=by rw[<- ssg c hc,<- J];exact w _ hS
  have O:u (bn c b)=0:=by have :=G _ r;simpa[d9] using this
  have N:u (bn c c)=0:=by rw[p];exact m
  by_cases D:c=0\/b=0
  .exact kP _ s c b hc RN D u' _ Re g N O (WN c hc u l) dm r
  obtain⟨rfl,t⟩:=ok2 c b hc RN D
  have e:Bm (0,1)=1/\Bm (0,b)=1:=by rcases t with rfl | rfl<;>simp[Bm]
  rw[e.1,e.2]at dm;exact hH _ s Lx M OW KR b t G u' _ Re g dm N O (WN 1 hc u l) r
 .subst W
  have r:d9 (single 0 1) (λj=> u (bn 0 j))∈L.map (ig 0):=by rw[<- ssg 0 hc,<- J];exact w _ hS
  have k:=F _ r;simp[d9]at k
  exact kDS _ s j' b C Z RN E Zl U H _ (by simpa[bn] using m) k (WN 0 hc u l) V r
 .have f:=R4 c hc L _ _ Oc;rw[ssg c hc]at f
  have r:d9 (single 0 1) (λj=> u (bn c j))∈L.map (ig c):=by
   rw[<- ssg c hc,<- J];exact w _ hS
  obtain⟨X,d,e⟩:=R3 c hc L Xg hXg
  have ai:∀ i,i≠0->X (i,c)=Bm (i,c):=λi K=> by
   have :=Vj (bn c i) (λh=> K (by rw[<- q i,h,p]))
   rw[e,q,B]at this;rw[this];fin_cases c<;>simp at hc<;>fin_cases i<;>simp[Bm,bn,T0]
  have SQ:∀ i,i≠0->ig c Xb (i,c)=Bm (i,c):=λi K=> by
   rw[Ip c hc,p,QM _ (λh=> K (by rw[<- q i,h,p]))]
   fin_cases c<;>simp at hc<;>fin_cases i<;>simp[Bm,bn,T0]
  have k1:=krh L hL P c hc Q hq R u _ m (by simpa[p] using Re) (WN c hc u' g) hS f Xb hXb QM X d ai
  have k2:=krh _ s Lx c hc M OW KR u' _ Re (by simpa[p] using m) (WN c hc u l) Oc r Xg hXg Vj
   _ (w _ hXb) SQ
  exact krf L hL c hc u _ m (by simpa[p] using Re) l (WN c hc u' g) hS f k1 (by simp only[q];exact k2)
def HE (X:Mt): Prop :=
 11*X (1,0)+11*X (1,2)+11*X (1,3)+11*X (2,0)+16*X (2,2)+11*X (2,3)+11*X (3,0)+11*X (3,2)
  +16*X (3,3)=0/\
 -48*X (1,0)+ X (1,2)+33*X (1,3)-48*X (2,0)+7*X (2,2)+33*X (2,3)-80*X (3,0)-15*X (3,2)
  +55*X (3,3)=0/\
 X (1,0)+3*X (1,2)+2*X (1,3)- X (2,0)+3*X (2,2)-2*X (2,3)=0/\
 -16*X (1,0)-5*X (1,2)+11*X (1,3)+16*X (2,0)-5*X (2,2)-11*X (2,3)=0/\
 3*X (1,0)*X (2,2)+2*X (1,0)*X (2,3)+2*X (1,0)*X (3,2)+3*X (1,0)*X (3,3)+3*X (1,2)*X (2,0)
  +3*X (1,2)*X (2,3)+2*X (1,2)*X (3,0)+3*X (1,2)*X (3,3)+2*X (1,3)*X (2,0)+3*X (1,3)*X (2,2)
  +3*X (1,3)*X (3,0)+3*X (1,3)*X (3,2)+3*X (2,0)*X (3,2)+3*X (2,0)*X (3,3)+3*X (2,2)*X (3,0)
  +5*X (2,2)*X (3,3)+3*X (2,3)*X (3,0)+5*X (2,3)*X (3,2)=0/\
 -16*X (1,0)*X (2,2)-16*X (1,0)*X (3,2)-16*X (1,2)*X (2,0)+11*X (1,2)*X (2,3)-16*X (1,2)*X (3,0)
  +11*X (1,2)*X (3,3)+11*X (1,3)*X (2,2)+11*X (1,3)*X (3,2)-32*X (2,0)*X (3,2)
  -32*X (2,2)*X (3,0)+22*X (2,2)*X (3,3)+22*X (2,3)*X (3,2)=0/\
 X (1,0)*X (2,2)+ X (1,2)*X (2,0)+2*X (1,2)*X (2,3)+2*X (1,3)*X (2,2)=0/\
 X (1,0)*X (2,2)*X (3,3)+ X (1,0)*X (2,3)*X (3,2)+ X (1,2)*X (2,0)*X (3,3)+ X (1,2)*X (2,3)*X (3,0)
  + X (1,3)*X (2,0)*X (3,2)+ X (1,3)*X (2,2)*X (3,0)=0
def hsE (L:Sq) (c:K5 L) (h3:d9 (single 3 1) (um 1 1 1 2)∈L)
  (h0:d9 (single 0 1) (um 11 16 0 3)∈L) (X:Mt) (d:X∈L) (o:∀ j,X (0,j)=0)
  (n:∀ i,X (i,1)=0):HE X:=by
 have a:=c _ d;have b:=c _ (L.neg_mem d);have k:=c _ (L.smul_mem 2 d);have e:=c _ (L.add_mem d h0);have f:=c _ (L.add_mem (L.neg_mem d) h0);have g:=c _ (L.add_mem d h3);have h:=c _ (L.add_mem (L.neg_mem d) h3);have l:=c _ (L.add_mem (L.add_mem d h3) h0);have m:=c _ (L.add_mem (L.add_mem (L.neg_mem d) h3) h0);simp +decide only[p4,d9,um,Bm,R5,Aa,Q6,Q5,
  Q4,o,n,R8,R9,Fin.isValue]at a b k e f g h l m
 exact⟨by linear_combination a- b/3- k/6,by linear_combination (b- a+ e- f)/2,
  by linear_combination (b- a+ g- h)/2,by linear_combination (a- b- e+ f- g+ h+ l- m)/2,
  by linear_combination (a+ b)/2,by linear_combination (e+ f- a- b)/2,
  by linear_combination (g+ h- a- b)/2,by linear_combination (k-3*a- b)/6⟩
def Wj (X:Mt) (h:HE X) (z:X (3,3)=0) (o:X (1,0)≠0\/X (1,2)≠0\/X (1,3)≠0\/X (2,0)≠0\/
  X (2,2)≠0\/X (2,3)≠0\/X (3,0)≠0\/X (3,2)≠0):False:=by
 obtain⟨a,b,c,d,e,f,g,i⟩:=h;rcases o with o | o | o | o | o | o | o | o<;>grind
def aoO (L:Sq) (a:K5 L) (u w:Fq->ℂ) (e:u 0=0) (m:u≠0)
  (f:w 1=0) (g:w 2=0) (n:w≠0) (b:d9 u (um 1 1 1 2)∈L) (c:d9 (single 0 1) w∈L):
  u 1=0/\u 2=0/\u 3≠0/\11*w 3= -16*w 0/\w 0≠0:=by
 have e1:=a _ b;have i:=a _ (L.neg_mem b);have e3:=a _ c;have k:=a _ (L.add_mem b c);have l:=a _ (L.add_mem (L.neg_mem b) c);have p:=Qm u e m
 have q:w 0≠0\/w 3≠0:=by
  by_contra h;push_neg at h;apply n;funext j;fin_cases j<;>simp[h.1,h.2,f,g]
 simp +decide only[p4,d9,um,Bm,R5,Aa,Q4,e,f,g,
  R8,R9,Fin.isValue]at e1 i e3 k l
 have d:u 1=0/\u 2=0:=by constructor<;>grind
 have o:11*w 3= -16*w 0:=by grind
 refine⟨d.1,d.2,by grind,o,by grind⟩
def hc2 (L:Sq) (c:K5 L) (B:finrank ℂ L=6)
  (F:finrank ℂ (L.map (af 0))=2) (G:finrank ℂ (L.map (Kl 1))=2) (u w:Fq->ℂ) (o:u 0=0)
  (x:u≠0) (q:w 1=0) (r:w 2=0) (y:w≠0) (e:d9 u (um 1 1 1 2)∈L)
  (f:d9 (single 0 1) w∈L):False:=by
 obtain⟨p1,p2,p3,A,H⟩:=aoO L c u w o x q r y e f
 have v:d9 (single 3 1) (um 1 1 1 2)∈L:=by
  convert L.smul_mem (u 3)⁻¹ e using 1;funext ⟨i,j⟩;fin_cases i<;>simp[d9,o,p1,p2,p3]
 have s:d9 (single 0 1) (um 11 16 0 3)∈L:=by
  convert L.smul_mem (11/w 0) f using 1;funext ⟨i,j⟩;fin_cases i<;>fin_cases j<;>simp[d9,um,q,r]<;>field_simp<;>
   first | grind
 have C:=dx L (af 0);have D:=dx L (Kl 1)
 have E:2≤ finrank ℂ ↥(Ar L 0 ⊓ iu L 1):=by
  have :=Bb (Ar L 0) (iu L 1);have :=W1 (sup_le (inf_le_left:Ar L 0≤ L) (inf_le_left:iu L 1≤ L));unfold Ar iu at *;omega
 have d:=dx (Ar L 0 ⊓ iu L 1) (LinearMap.proj (R:= ℂ) (φ:=λ_:Fq× Fq=> ℂ) (3,3))
 have t:=Z7 ((Ar L 0 ⊓ iu L 1).map (LinearMap.proj (R:= ℂ) (φ:=λ_:Fq× Fq=> ℂ) (3,3)))
 rw[Bi]at t;obtain⟨n,hn,hn0⟩:=Bt (p:=Ar L 0 ⊓ iu L 1 ⊓
  ker (LinearMap.proj (R:= ℂ) (φ:=λ_:Fq× Fq=> ℂ) (3,3))) (by
   intro h;rw[h,V3]at d;omega)
 obtain⟨⟨hnA,hnB⟩,l⟩:=U1.1 hn |>.imp_left U1.1;obtain⟨k,m⟩:=(ei L 0 n).1 hnA;have g:=((ti L 1 n).1 hnB).2
 have z:n (3,3)=0:=by simpa using l
 refine Wj n (hsE L c v s n k m g) z ?_;by_contra a;push_neg at a
 exact hn0 (funext λ⟨i,j⟩=> by fin_cases i<;>fin_cases j<;>simp[m,g,z,a])
def aik:abU:=by
 intro L c b g hq _ x o _ u w l hu d m n k hS;rcases o with rfl | rfl
 .exact hc2 L c b g hq u w l hu m n k d hS
 let a:Equiv.Perm (Fq):=swap 2 3
 have e:(L.map (gp a)).map (Kl 1)=((L.map Mv).map (gp a)).map (af 1):=by
  simp only[<- Y4];congr 1
 have p:a.symm 0=0:=by rw[Cm];exact Cz (by decide) (by decide)
 have q:a.symm 1=1:=by rw[Cm];exact Cz (by decide) (by decide)
 refine hc2 (L.map (gp a)) (LY L c a) (by rw[o6];exact b)
  (by rw[KW,p];exact g) (by rw[e,KW,q,<- Y4];exact hq) (λi=> u (a i))
  (λj=> w (a j)) (by simpa[a,T0] using l)
  (λh=> hu (funext λi=> by have :=congrFun h (a i);simpa[a] using this)) (by simpa[a,T0] using m)
  (by simpa[a] using n) (λh=> k (funext λi=> by have :=congrFun h (a i);simpa[a] using this)) ?_ ?_
 .convert S8 (f:=gp a) d using 1;funext ⟨i,j⟩;fin_cases j<;>simp[my,d9,um,a,T0]
 .convert S8 (f:=gp a) hS using 1;funext ⟨i,j⟩;fin_cases i<;>fin_cases j<;>simp[my,d9,a,T0]
def abP:E3p:=afP aik
def E2N: Prop := ∀ L:Sq,(∀ t∈L,p4 (Bm+ t)=65)->finrank ℂ L=6-> ∀ c:Fq,c.val<2->
 finrank ℂ (L.map (af 0))=2->finrank ℂ (L.map (Kl c))=2->(∃ X∈L,X (0,c)≠0)->False
def apq (N:Sq) (k:ℕ) (h:k≤ finrank ℂ N):∃ W≤ N,finrank ℂ W=k:=by
 let b:=Module.finBasis ℂ N
 have a:LinearIndependent ℂ (λi:Fin k=>(b (Fin.castLEEmb h i):Mt)):=
  (b.linearIndependent.comp _ (Fin.castLEEmb h).injective).map' N.subtype N.ker_subtype
 refine⟨span ℂ (Set.range λi:Fin k=>(b (Fin.castLEEmb h i):Mt)),?_,?_⟩
 .rw[Submodule.span_le];rintro _ ⟨i,rfl⟩;exact (b _).2
 .rw[Bq a];simp
def p5r (f:aaU) (L:Sq) (d:∀ t∈L,p4 (Bm+ t)=65) (c:finrank ℂ L=6) (r:Fq)
  (h:finrank ℂ (L.map (af r))≤1):False:=by
 set M:=L.map (gp (swap r 0));have e:∀ t∈M,p4 (Bm+ t)=65:=LY L d _
 have k:finrank ℂ (M.map (af 0))≤1:=by rw[KW,Cm,Equiv.swap_apply_right];exact h
 have l:finrank ℂ (M.map (af 0))+ finrank ℂ ↥(Ar M 0)=finrank ℂ M:=dx M (af 0)
 have Lx:finrank ℂ M=6:=by rw[o6];exact c
 obtain⟨W,a,b⟩:=apq (Ar M 0) 5 (by omega)
 exact f W (λt i=> e t ((ei M 0 t).1 (a i)).1) b (λX g j=>((ei M 0 X).1 (a g)).2 j)
def abN (e:aaU) (g:E3p) (i:E2N) (L:Sq) (b:∀ t∈L,p4 (Bm+ t)=65)
  (a:finrank ℂ L=6) (c:Fq) (f:c.val<2) (j:finrank ℂ (L.map (af 0))≤2)
  (k:finrank ℂ (L.map (Kl c))≤2):False:=by
 rcases Nat.lt_or_ge (finrank ℂ (L.map (af 0))) 2 with h | h
 .exact p5r e L b a 0 (by omega)
 rcases Nat.lt_or_ge (finrank ℂ (L.map (Kl c))) 2 with h' | h'
 .refine p5r e (L.map Mv) (QR L b) (by rw[Qv];exact a) c ?_
  rw[<- Y4];exact (by omega :finrank ℂ (L.map (Kl c))≤1)
 by_cases d:∀ X∈L,X (0,c)=0
 .exact g L b a c f (by omega) (by omega) d
 .push_neg at d
  exact i L b a c f (by omega) (by omega) d
def abM (i:aaU) (f:E3p) (g:E2N):Q7:=by
 rintro L h h6 ⟨r,k⟩ ⟨c,j⟩;obtain⟨a,b,d⟩:=ZM r c
 refine abN i f g (L.map (gp a)) (LY L h a) (by rw[o6];exact h6) (a c) d
  (by rw[KW,<- b,Da];exact k) ?_
 have e:(L.map (gp a)).map (Kl (a c))=((L.map Mv).map (gp a)).map (af (a c)):=by
  simp only[<- Y4];congr 1
 rw[e,KW,Da];exact j
abbrev cq:=Ft->ℂ
abbrev Nv (q:cq): Prop :=(q 0≠0/\q 1≠0)\/(q 0≠0/\q 2≠0)\/(q 1≠0/\q 2≠0)
def YM {k:ℕ} (N:Submodule ℂ (Ft× Ft->ℂ)) (G:Matrix (Ft× Ft) (Ft× Ft) ℂ)
  (q:Function.Injective G.mulVec) (v:Fin k->(Ft× Ft->ℂ)) (hv:LinearIndependent ℂ v)
  (A:9< finrank ℂ N+ finrank ℂ N+ k) (s:∀ n∈N,∀ i,dotProduct (v i) n=0)
  (f:∀ n∈N,∀ e∈N,dotProduct n (G.mulVec e)=0):
  ∃ m∈N,m≠0/\G.mulVec m∈span ℂ (Set.range v):=by
 have g:∀ a∈N,∀ b∈N.map (Matrix.mulVecLin G) ⊔ span ℂ (Set.range v),dotProduct a b=0:=by
  intro a ha b hb;obtain⟨x,hx,y,c,rfl⟩:=V0.1 hb;obtain⟨e,Ni,rfl⟩:=hx
  have d:dotProduct a y=0:=by
   refine Submodule.span_induction (p:=λy _=> dotProduct a y=0) ?_ ?_ ?_ ?_ c
   .rintro _ ⟨i,rfl⟩;rw[Ah];exact s a ha i
   .simp
   .intro x y _ _ hx c;rw[Bu,hx,c,S0]
   .intro r x _ hx;rw[Co,hx,Z6]
  rw[Bu,d,S0,Db];exact f a ha e Ni
 have l:=Sw N _ g;have w:finrank ℂ (N.map (Matrix.mulVecLin G))=finrank ℂ N:=
  (Y3 (equivMapOfInjective (Matrix.mulVecLin G) q N)).symm
 have z:finrank ℂ (span ℂ (Set.range v))=k:=by rw[Bq hv,Bc]
 have o:=Bb (N.map (Matrix.mulVecLin G)) (span ℂ (Set.range v));simp only[Fintype.card_prod,Bc]at l
 have u:N.map (Matrix.mulVecLin G) ⊓ span ℂ (Set.range v)≠ ⊥ :=by
  intro h;rw[h,V3]at o;omega
 obtain⟨y,c,d⟩:=Bt u;obtain⟨hyM,j⟩:=U1.1 c;obtain⟨m,t,rfl⟩:=hyM
 refine⟨m,t,λh=> d (by rw[h,map_zero]),?_⟩
 rw[<- Db];exact j
def o0 (a b:Ft):B9:=single (a,b) 1
def eh (c:Fq):B9:=λp=> if rR p.1=bn c (rR p.2) then 16 else 11
def LN:Ft->Ft->Ft:= ![![0,2,1],![2,0,0],![1,0,0]]
def lj (c:Fq):Matrix (Ft× Ft) (Ft× Ft) ℂ:=λp q=>
 if p.1=q.1\/p.2=q.2 then 0 else Bm (0,c)*Bm (rR (LN p.1 q.1),bn c (rR (LN p.2 q.2)))+
  Bm (0,bn c (rR (LN p.2 q.2)))*Bm (rR (LN p.1 q.1),c)
def gH (c:Fq) (M:Submodule ℂ B9): Prop :=3≤ finrank ℂ M/\(∀ m∈M,dotProduct (eh c) m=0)/\
 (∀ m∈M,∀ a∈M,dotProduct m ((lj c).mulVec a)=0)/\ ∀ m∈M,p3 m=0
def UO (c:Fq) (g:ℂ) (j:Fin 10):Fq->B9:=
 ![eh c,![o0 0 1,o0 0 1,o0 1 1,o0 1 1,o0 1 1,o0 1 1,o0 2 2,o0 2 2,o0 2 2,o0 2 2] j,
  ![o0 0 2,o0 0 2,o0 1 2,o0 1 2,o0 2 1,o0 2 1,o0 1 2,o0 1 2,o0 2 1,o0 2 1] j,
  ![o0 0 0,o0 1 2+ o0 2 2- g•(o0 1 1+ o0 2 1),o0 2 1+ o0 2 2,Bm (0,c)•o0 0 2-(3:ℂ)•o0 2 2,
   o0 1 2+ o0 2 2,Bm (0,c)•o0 0 2+(3:ℂ)•o0 1 2-(3:ℂ)•o0 2 2,o0 0 2,o0 1 1+ o0 2 1,
   o0 1 1+ o0 1 2,Bm (0,c)•o0 0 2+(3:ℂ)•o0 1 2] j]
def Vf {c:Fq} (b:c.val<2):Function.Injective (lj c).mulVec:=by
 have k:∀ m:B9,(lj c).mulVec m=0->m=0:=λm h=> by
  have a:=λp=> congrFun h p
  rcases I7 c b with rfl | rfl<;>simp +decide [LN,lj,mulVec,dotProduct,S6,
   S9,Bm,rR,bn,Prod.forall,U3,Bd]at a ⊢ <;>grind
 exact λx y e=> Bn.1 (k _ (by rw[Matrix.mulVec_sub,e,Aj]))
set_option maxHeartbeats 0 in
def ahh {c:Fq} (d:c.val<2) g j (m:B9) (a:Fq->ℂ)
 (h:(lj c).mulVec m= ∑ t,a t•UO c g j t) (h':∀ t,dotProduct (UO c g j t) m=0)
 (r:Qf ![1,0,0] ![1,0,0] m=0):m=0/\a=0:=by
 have b:=λp=> congrFun h p
 rcases I7 c d with rfl | rfl<;>simp +decide [LN,lj,mulVec,dotProduct,S6,S9,Bm,rR,bn,Prod.forall,U3]at b h'<;>fin_cases j<;>
  simp +decide [UO,eh,o0,Q4,Prod.forall,U3,Bd,Qf,ah,S9,rR,bn,Bm]at b h' r ⊢ <;>
  grind (splits :=16)
def XD (c:Fq):Mt:=λq=> if q.2=bn c 1 then (if q.1=2 then 11 else if q.1=3 then -11 else 0) else 0
set_option maxHeartbeats 0 in
def anL {c:Fq} (e:c.val<2) {n a:Mt} (g:∀ j,n (0,j)=0) (f:∀ i,n (i,c)=0)
 (b:∀ j,a (0,j)=0) (d:∀ i,a (i,c)=0):
 8*(p4 (Bm+ n)- p4 (Bm+ -n))-(p4 (Bm+(2:ℂ)•n)- p4 (Bm+(-2:ℂ)•n))=12*dotProduct (eh c) (dq c n)/\
 p4 (Bm+(2:ℂ)•n)- p4 (Bm+(-2:ℂ)•n)-2*(p4 (Bm+ n)- p4 (Bm+ -n))=12*Bm (0,c)*p3 (dq c n)/\
 p4 (Bm+(n+ a))- p4 (Bm+(n- a))- p4 (Bm+(-n+ a))+ p4 (Bm+(-n- a))=
  4*dotProduct (dq c n) ((lj c).mulVec (dq c a)):=by
 refine⟨?_,?_,?_⟩<;>rcases I7 c e with rfl | rfl<;>
  simp[p4,Bm,eh,lj,LN,dq,rR,bn,dotProduct,mulVec,S6,S9,
   p3,g,f,b,d,T0]<;>ring
set_option maxHeartbeats 0 in
lemma ahj {c:Fq} (a:c.val<2) (M:B9):dotProduct M ((lj c).mulVec (dq c (XD c)))=
 11*(Bm (0,c)*(M (0,1)- M (0,2))-3*M (1,1)-3*M (1,2)+3*M (2,1)+3*M (2,2))/\
 p3 (M+ dq c (XD c))- p3 M=11*(M (0,1)*M (2,2)+ M (0,2)*M (2,1)- M (0,1)*M (1,2)- M (0,2)*M (1,1)):=by
 refine⟨?_,?_⟩<;>rcases I7 c a with rfl | rfl<;>
  simp[p3,Bm,lj,LN,dq,XD,rR,bn,dotProduct,mulVec,S6,S9,
   T0]<;>ring
def anN (k g x0 x1 x2 x3 f c m x7 x8:ℂ)
 (i:x1*c+ x2*f=0) (j:x1*x8+ x2*x7=0) (r1:f*x8+ c*x7=0)
 (n:x0*(c+ x8)+ x2*(x3+ m)- g*(x0*(f+ x7)+ x1*(x3+ m))=0)
 (l:k*(x1- x2)-3*f-3*c+3*x7+3*x8=0):
 (x1=0/\x2=0/\(x0=0\/c+ x8- g*(f+ x7)=0))\/(f=0/\c=0/\(x7+ x8=0\/k*x2-3*x8=0))\/
 (f=0/\x7=0/\(c+ x8=0\/k*x2+3*c-3*x8=0))\/(x8=0/\c=0/\(x2=0\/f+ x7=0))\/
 (x8=0/\x7=0/\(f+ c=0\/k*x2+3*c=0)):=by
 by_cases h:x1=0/\x2=0
 · obtain⟨a,b⟩:=h;subst a b
   rcases Q3.1 (show x0*(c+ x8- g*(f+ x7))=0 by linear_combination n) with e | e<;>simp[e]
 have d:c*x7- f*x8=0:=by
  rcases not_and_or.1 h with h | h
  .exact (Q3.1 (show (c*x7- f*x8)*x1=0 by linear_combination x7*i- f*j)).resolve_right h
  .exact (Q3.1 (show (c*x7- f*x8)*x2=0 by linear_combination c*j- x8*i)).resolve_right h
 rcases Q3.1 (show c*x7=0 by linear_combination (d+ r1)/2) with a | a<;>
  rcases Q3.1 (show f*x8=0 by linear_combination (r1- d)/2) with b | b<;>subst a b<;>
  [rcases Q3.1 (show (x7+ x8)*(k*x2-3*x8)=0 by linear_combination k*j- x8*l) with e | e;
   rcases Q3.1 (show x2*(f+ x7)=0 by linear_combination i+ j) with e | e;
   rcases Q3.1 (show (c+ x8)*(k*x2+3*c-3*x8)=0 by
    linear_combination k*(i+ j)-(c+ x8)*l) with e | e;
   rcases Q3.1 (show (f+ c)*(k*x2+3*c)=0 by linear_combination k*i- c*l) with e | e]<;>
  simp[e]
set_option maxHeartbeats 0 in
def anM {c:Fq} (hc:c.val<2) {g:ℂ} {M:B9} (i:dotProduct (eh c) M=0)
 (l:dotProduct M ((lj c).mulVec (dq c (XD c)))=0) (pr:p3 (M+ dq c (XD c))- p3 M=0)
 (f:Qf ![1,0,0] ![1,0,0] M=0) (d:Qf ![0,1,1] ![1,0,0] M=0)
 (q3:Qf ![0,1,1] ![0,1,-g] M=0):∃ j,∀ t,dotProduct (UO c g j t) M=0:=by
 have e:∀ a b,dotProduct (o0 a b) M=M (a,b):=λa b=> by simp[o0,dotProduct,Q4]
 rw[(ahj hc M).1]at l;rw[(ahj hc M).2]at pr;simp[Qf,ah,R1]at f d q3;rcases anN (Bm (0,c)) g (M (0,0)) (M (0,1)) (M (0,2)) (M (1,0)) (M (1,1)) (M (1,2)) (M (2,0)) (M (2,1)) (M (2,2))
  (by linear_combination d/2- pr/22) (by linear_combination d/2+ pr/22) (by linear_combination f)
  (by linear_combination q3) (by linear_combination l/11) with⟨a,b,h | h⟩ | ⟨a,b,h | h⟩ | ⟨a,b,h | h⟩ | ⟨a,b,h | h⟩ | ⟨a,b,h | h⟩<;>
  [refine⟨0,?_⟩;refine⟨1,?_⟩;refine⟨2,?_⟩;refine⟨3,?_⟩;refine⟨4,?_⟩;refine⟨5,?_⟩;
   refine⟨6,?_⟩;refine⟨7,?_⟩;refine⟨8,?_⟩;refine⟨9,?_⟩]<;>intro t<;>(fin_cases t;exact i)<;>simp[UO,e]<;>grind
def ahl {c:Fq} (hc:c.val<2) {n:Mt} (f:∀ j,n (0,j)=0) (d:∀ i,n (i,c)=0)
 (h:dq c n=0):n=0:=by
 funext ⟨i,j⟩
 have e:=λa b=> congrFun h (a,b)
 rcases I7 c hc with rfl | rfl<;>simp[U3,dq,rR,bn,T0]at e<;>
  fin_cases i,j<;>simp_all
def ahk (c:Fq) (e:c.val<2) M (H:gH c M) (h:dq c (XD c)∈M) (g:ℂ)
 (l:∀ m∈M,Qf ![1,0,0] ![1,0,0] m=0) (v:∀ m∈M,Qf ![0,1,1] ![1,0,0] m=0)
 (w:∀ m∈M,Qf ![0,1,1] ![0,1,-g] m=0):False:=by
 obtain⟨h3,p,d,k⟩:=H
 have u:∀ m∈M,∃ j,∀ t,dotProduct (UO c g j t) m=0:=λm hm=>
  anM e (p m hm) (d m hm _ h) (by rw[k _ (M.add_mem hm h),k m hm,X4]) (l m hm) (v m hm) (w m hm)
 obtain⟨j,f⟩:∃ j,∀ m∈M,∀ t,dotProduct (UO c g j t) m=0:=by
  by_contra H;push_neg at H
  let K:Fin 10->Subspace ℂ ↥M:=λj=>
   ker ((Matrix.of (UO c g j)).mulVecLin∘ₗ M.subtype)
  have o:(⊤ :Subspace ℂ ↥M)∉ Finset.univ.image K:=by
   simp only[Finset.mem_image,Cp,true_and,not_exists];intro j i;obtain⟨n,hn,t,q⟩:=H j;have :(⟨n,hn⟩: ↥M)∈K j:=i ▸ Au;exact q (congrFun (Am.1 this) t)
  obtain⟨a,b⟩:=(Set.ne_univ_iff_exists_notMem _).1 (Subspace.biUnion_ne_univ_of_top_notMem o);obtain⟨j,f⟩:=u a a.2;exact b (Set.mem_iUnion₂.2 ⟨K j,Finset.mem_image_of_mem K (Cp j),
   by rw[SetLike.mem_coe];exact Am.2 (funext f)⟩)
 have hv:LinearIndependent ℂ (UO c g j):=Ax.2 λa b=>
  congrFun (ahh e g j 0 a (by rw[Bv,b]) (λt=> dotProduct_zero _) (by simp[Qf])).2
 obtain⟨m,hm,s,d⟩:=YM M (lj c) (Vf e) (UO c g j) hv (by show 9< finrank ℂ ↥M+ finrank ℂ ↥M+4;omega) (λx r t=> f x r t) d
 obtain⟨a,b⟩:=(An ℂ).1 d;exact s (ahh e g j _ a b.symm (f m hm) (l m hm)).1
def bj (a b:cq):B9:=λp=> a p.1*b p.2
def oj (a:cq):cq:= ![a 1*a 2,a 0*a 2,a 0*a 1]
def SM (c:Fq) (i j:Ft):ℂ:=Bm (0,c)*Bm (rR i,bn c (rR j))+ Bm (0,bn c (rR j))*Bm (rR i,c)
lemma YP {c:Fq} (a:c.val<2) i j:SM c i j≠0:=by
 rcases I7 c a with rfl | rfl<;>fin_cases i,j<;>norm_num[SM,Bm,rR,bn,T0]
lemma Mm:∀ o i:Ft,ah o 0≠o/\ah o 1≠o/\ah o 1≠ah o 0/\(i=o\/i=ah o 0\/i=ah o 1):=by
 decide
def aa6 a b (B:B9):
 p3 (B+ bj a b)- p3 (B- bj a b)=2*Qf a b B+12*(a 0*a 1*a 2)*(b 0*b 1*b 2):=by
 simp[p3,Qf,bj,ah,R1];ring
def anO a b (B:B9):
 p3 (bj a b+ B)- p3 (bj a b- B)=4* ∑ i,oj a i* ∑ j,B (i,j)*oj b j+2*p3 B:=by
 simp[p3,bj,oj,R1];ring
def gP3 {M:Submodule ℂ B9} (d:∀ m∈M,p3 m=0) a b (h:bj a b∈M) (m:B9) (c:m∈M):
 ∑ i,oj a i* ∑ k,m (i,k)*oj b k=0:=by
 have :=anO a b m;rw[d _ (M.add_mem h c),d _ (M.sub_mem h c),d m c]at this;linear_combination -this /4
lemma Vg (a b u v:cq) (B:B9):Qf u v (bj a b+ B)- Qf u v (bj a b)- Qf u v B=
 ∑ i,(∑ k,j1 a i k*u k)* ∑ j,B (i,j)* ∑ l,j1 b j l*v l:=by
 simp[Qf,bj,j1,ah,R1];ring
lemma ahm {c a b a' b'}:dotProduct (bj a b) ((lj c).mulVec (bj a' b'))=
 ∑ r,∑ s,(∑ k,j1 a r k*a' k)*SM c r s*(∑ l,j1 b s l*b' l):=by
 simp[bj,lj,SM,LN,j1,mulVec,dotProduct,S6,S9];ring
lemma Xe {o:Ft} (y:cq) {u B:cq} (b:y o=0) (a:u o=0):
 ∑ i,(∑ k,j1 y i k*u k)*B i=(y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0))*B o:=by
 fin_cases o<;>simp[j1,ah,R1]at b a ⊢ <;>rw[b,a]<;>ring
lemma aa5 c {o:Ft} {a:cq} b {a':cq} b' (e:a o=0) (d:a' o=0):
 dotProduct (bj a b) ((lj c).mulVec (bj a' b'))=
  (a (ah o 0)*a' (ah o 1)+ a (ah o 1)*a' (ah o 0))* ∑ s,SM c o s* ∑ l,j1 b s l*b' l:=by
 rw[ahm];simp only[X8,<- Ao];rw[Xe a e d]
lemma ahn c {o:Ft} a {b:cq} a' {d:cq} (f:b o=0) (e:d o=0):
 dotProduct (bj a b) ((lj c).mulVec (bj a' d))=
  (b (ah o 0)*d (ah o 1)+ b (ah o 1)*d (ah o 0))* ∑ r,SM c r o* ∑ k,j1 a r k*a' k:=by
 rw[ahm];fin_cases o<;>simp[j1,ah,R1]at f e ⊢ <;>rw[f,e]<;>ring
lemma Xd {o:Ft} {y:cq} (B:cq) (a:y o=0): ∑ i,oj y i*B i=y (ah o 0)*y (ah o 1)*B o:=by
 fin_cases o<;>simp[oj,ah,R1]at a ⊢ <;>rw[a]<;>ring
lemma adB {a b} {u v:cq}:Qf u v (bj a b)=2*(∑ i,oj a i*u i)*(∑ j,oj b j*v j):=by
 simp[Qf,bj,oj,ah,R1];ring
def adD (φ:cq) {q} (a:∀ i,φ i≠0) (b:Nv q)
 (h: ∑ s,φ s* ∑ l,j1 q s l*q l=0):∀ i,q i≠0:=by
 have :=a 0;have :=a 1;have :=a 2
 have :q 0≠0/\q 1≠0/\q 2≠0:=by
  refine⟨λe=> ?_,λe=> ?_,λe=> ?_⟩<;>simp[e,j1,R1]at h<;>grind
 intro i;fin_cases i<;>simp[this]
set_option maxHeartbeats 0 in
def aht {c:Fq} (d:c.val<2) o (m:B9) (a:Fq->ℂ)
 (h:(lj c).mulVec m= ∑ t,a t• ![eh c,o0 o 0,o0 o 1,o0 o 2] t)
 (h':∀ t,dotProduct (![eh c,o0 o 0,o0 o 1,o0 o 2] t) m=0):m=0/\a=0:=by
 have b:=λp=> congrFun h p
 rcases I7 c d with rfl | rfl<;>simp +decide [LN,lj,eh,mulVec,dotProduct,S6,S9,Bm,rR,bn,Prod.forall,U3]at b h' ⊢ <;>fin_cases o<;>
  simp +decide [eh,o0,S9,Q4,Bm,rR,bn,Prod.forall,U3,Bd]at b h' ⊢ <;>grind
def ahu {c:Fq} (b:c.val<2) {M:Submodule ℂ B9} (k:3≤ finrank ℂ M)
 (d:∀ m∈M,dotProduct (eh c) m=0) (h:∀ m∈M,∀ i∈M,dotProduct m ((lj c).mulVec i)=0)
 (o:Ft) (g:∀ m∈M,∀ t,m (o,t)=0):False:=by
 have hv:LinearIndependent ℂ ![eh c,o0 o 0,o0 o 1,o0 o 2]:=Ax.2 λa ha=>
  congrFun (aht b o 0 a (by rw[Bv,ha]) (λt=> dotProduct_zero _)).2
 obtain⟨m,f,j,e⟩:=YM M (lj c) (Vf b) _ hv (by show 9< finrank ℂ ↥M+ finrank ℂ ↥M+4;omega)
  (λn hn t=> by fin_cases t<;>simp[o0,dotProduct,Q4,g n hn]<;>exact d n hn)
  h
 obtain⟨a,ha⟩:=(An ℂ).1 e
 exact j (aht b o m a ha.symm (λt=> by
  fin_cases t<;>simp[o0,dotProduct,Q4,g m f]<;>exact d m f)).1
def aeH a b (B:B9):
 p3 (bj a b+ B)- p3 (bj a b- B)=4* ∑ i,∑ j,B (i,j)*(oj a i*oj b j)+2*p3 B:=by
 simp[p3,bj,oj,R1];ring
def akn (a b u v:cq) (B:B9):Qf u v (bj a b+ B)- Qf u v (bj a b)- Qf u v B=
 ∑ i,∑ j,(∑ k,j1 a i k*u k)*B (i,j)*(∑ l,j1 b j l*v l):=by
 simp[Qf,bj,j1,ah,R1];ring
def LF (c:Fq) (d o:Ft) (s:ℂ):cq:=λi=>
 if i=o then 0 else if i=ah o 0 then eh c (ah o 1,d) else s*eh c (ah o 0,d)
lemma aeJ (o:Ft) {g:cq}: ∑ i,g i=g o+ g (ah o 0)+ g (ah o 1):=by
 fin_cases o<;>simp[R1,ah]<;>ring
lemma aho {o:Ft} (d:Ft) w {y:cq} (q u:cq) (a:y o=0):
 ∑ i,∑ j,bj w (single d 1) (i,j)*(oj y i*oj q j)=w o*(y (ah o 0)*y (ah o 1))*oj q d/\
 Qf u (single d 1) (bj y q)=2*(u o*(y (ah o 0)*y (ah o 1)))*oj q d:=by
 constructor<;>fin_cases o,d<;>simp[bj,oj,Qf,ah,R1,Q4]at a ⊢ <;>
  rw[a]<;>ring
set_option maxHeartbeats 0 in
def anB {c:Fq} (f:c.val<2) {d o:Ft} {w y q}
 (a:dotProduct (bj y q) ((lj c).mulVec (bj y q))=0)
 (g:dotProduct (bj w (single d 1)) ((lj c).mulVec (bj y q))=0) (yo:y o=0) (b:y (ah o 0)≠0)
 (yb:y (ah o 1)≠0) (h:Nv q):
 oj q d≠0/\(w o=0->y (ah o 0)*w (ah o 1)+ y (ah o 1)*w (ah o 0)=0):=by
 have e:oj q d≠0:=by
  rcases I7 c f with rfl | rfl<;>simp +decide [lj,LN,mulVec,dotProduct,S6,S9,Bm,rR,bn]at a h b yb yo ⊢ <;>fin_cases d,o<;>
   simp +decide [bj,oj,S9,Bm,rR,bn,ah]at a h b yb yo ⊢ <;>grind
 refine⟨e,λi=> ?_⟩
 rcases I7 c f with rfl | rfl<;>simp +decide [lj,LN,mulVec,dotProduct,S6,S9,Bm,rR,bn]at g a e i yo b yb ⊢ <;>fin_cases d,o<;>
  simp +decide [bj,oj,S9,Q4,Bm,rR,bn,ah]at g a e i yo b yb ⊢ <;>grind
def SN (o d:Ft) (q:cq) (x:ℂ) (m:B9):B9:=λp=>
 if p.1=o then (if p.2=d then 0 else if p.2=ah d 0 then x*q (ah d 0) else -(x*q (ah d 1))) else m p
def anR {o d:Ft} {q} {y:cq} {m:B9} (c:y o=0)
 (a: ∑ i,∑ j,m (i,j)*(oj y i*oj q j)=0)
 (b: ∑ j,m (o,j)* ∑ l,j1 q j l*(single d 1:cq) l=0):
 m (o,d)*(y (ah o 0)*y (ah o 1)*oj q d)=0/\m (o,ah d 0)*q (ah d 1)+ m (o,ah d 1)*q (ah d 0)=0/\
 oj q d=q (ah d 0)*q (ah d 1):=by
 refine⟨?_,?_,?_⟩<;>fin_cases o,d<;>
  simp[oj,j1,ah,R1,Q4]at c a b ⊢ <;>grind
set_option maxHeartbeats 0 in
def anA {c:Fq} (a:c.val<2) {d o} {q:cq} {x m}
 (p2:dotProduct (eh c) (bj (LF c d o 1) q)=0)
 (g:dotProduct (bj (LF c d o 1) q) ((lj c).mulVec (bj (LF c d o 1) q))=0) (j:oj q d≠0)
 (h:dotProduct (eh c) (SN o d q x m)=0)
 (i:dotProduct (SN o d q x m) ((lj c).mulVec (bj (LF c d o (-1)) (single d 1)))=0)
 (b:dotProduct (SN o d q x m) ((lj c).mulVec (bj (LF c d o 1) q))=0)
 (e:Qf (LF c d o (-1)) (single d 1) (SN o d q x m)=0) (f:Qf (LF c d o 1) q (SN o d q x m)=0):
 x=0:=by
 rcases I7 c a with rfl | rfl<;>simp +decide [lj,LN,mulVec,dotProduct,S6,S9,Bm,rR,bn]at * <;>fin_cases d,o<;>
  simp +decide [SN,LF,bj,oj,eh,Q4,Bm,rR,bn,Qf,ah,S9]at * <;>grind
def anz (c:Fq) (B:c.val<2) M (H:gH c M) (d o:Ft) (w y q u:cq) (n:bj w (single d 1)∈M)
 (hw:w 0≠0\/w 1≠0\/w 2≠0) (g:bj y q∈M) (x:y o=0) (ya:y (ah o 0)≠0) (G:y (ah o 1)≠0)
 (hq:Nv q) (hu:∀ m∈M,Qf u (single d 1) m=0)
 (NG:u o≠0\/y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0)≠0):False:=by
 obtain⟨h3,hF,hG,hp⟩:=H;have P3:∀ a b,bj a b∈M-> ∀ m∈M,p3 (bj a b+ m)- p3 (bj a b- m)=0/\
   p3 (m+ bj a b)- p3 (m- bj a b)=0:=λa b h m hm=> by
  rw[hp _ (M.add_mem h hm),hp _ (M.sub_mem h hm),hp _ (M.add_mem hm h),hp _ (M.sub_mem hm h)];simp
 have Q:=aeH y q (bj w (single d 1));rw[(P3 y q g _ n).1,hp _ n,(aho d w q u x).1]at Q;obtain⟨r,C⟩:=anB B (hG _ g _ g) (hG _ n _ g) x ya G hq
 have F:w o=0:=by simpa[ya,G,r] using (by linear_combination -Q/4:w o*(y (ah o 0)*y (ah o 1))*oj q d=0)
 have Z:u o=0:=by have :=hu _ g;rw[(aho d w q u x).2]at this;simpa[ya,G,r] using this
 obtain⟨T,U,V,-⟩:=Mm o 0
 have z:∀ p,eh c p≠0:=λp=> by simp only[eh];split_ifs<;>norm_num
 have e:=hF _ n;simp[dotProduct,bj,S6,Q4]at e;rw[aeJ o,F]at e
 have wa:w (ah o 0)≠0:=λA=> by
  have R:w (ah o 1)=0:=by
   rw[A]at e;simpa[z] using (by linear_combination e:eh c (ah o 1,d)*w (ah o 1)=0)
  have :∀ i,w i=0:=λi=> by rcases (Mm o i).2.2.2 with rfl | rfl | rfl<;>assumption
  rcases hw with h | h | h<;>exact h (this _)
 replace C:=C F
 have L:eh c (ah o 0,d)*y (ah o 0)=eh c (ah o 1,d)*y (ah o 1):=by
  have :w (ah o 0)*(eh c (ah o 1,d)*y (ah o 1)- eh c (ah o 0,d)*y (ah o 0))=0:=by
   linear_combination eh c (ah o 1,d)*C- y (ah o 0)*e
  linear_combination -(Q3.1 this).resolve_left wa
 have W:∀ (v:cq) (s k:ℂ),v o=0->eh c (ah o 1,d)=k*v (ah o 0)->
   s*eh c (ah o 0,d)=k*v (ah o 1)->LF c d o s=k•v:=λv s k A ha R=> by
  funext i;rcases (Mm o i).2.2.2 with rfl | rfl | rfl
  .simp[LF,A]
  .simpa[LF,T] using ha
  .simpa[LF,U,V] using R
 have Rk:∀ (v b:cq) (k:ℂ),bj (k•v) b=k•bj v b:=λv b k=> by funext p;simp[bj,X8]
 have J:=W y 1 (eh c (ah o 1,d)/y (ah o 0)) x (by field_simp)
  (by rw[Be,Bw ya];linear_combination L)
 have K:bj (LF c d o (-1)) (single d 1)∈M:=by
  rw[W w (-1) (eh c (ah o 1,d)/w (ah o 0)) F (by field_simp)
   (by rw[Be,Bw wa];linear_combination -e),Rk];exact M.smul_mem _ n
 have f:bj (LF c d o 1) q∈M:=by rw[J,Rk];exact M.smul_mem _ g
 have k:LF c d o 1 (ah o 0)*u (ah o 1)+ LF c d o 1 (ah o 1)*u (ah o 0)≠0:=by
  have k0:=NG.resolve_left (by simp[Z])
  rw[J];simp only[Q6,Q5];intro h;apply k0
  have :eh c (ah o 1,d)/y (ah o 0)*(y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0))=0:=by
   linear_combination h
  exact (Q3.1 this).resolve_left (div_ne_zero (z _) ya)
 have X:∀ (a:cq) (i:Ft),a i=0->a 0*a 1*a 2=0:=λa i h=> by
  simpa[Fin.prod_univ_three] using Finset.prod_eq_zero (Cp i) h
 refine ahu B h3 hF hG o λm hm t=> ?_
 have h6: ∑ i,∑ j,m (i,j)*(oj (LF c d o 1) i*oj q j)=0:=by
  have :=aeH (LF c d o 1) q m;rw[(P3 _ q f m hm).1,hp m hm]at this;linear_combination -this /4
 have h7: ∑ j,m (o,j)* ∑ l,j1 q j l*(single d 1:cq) l=0:=by
  have :=akn (LF c d o 1) q u (single d 1) m;rw[hu _ (M.add_mem f hm),hu _ f,hu _ hm]at this;simp only[X8,<- Ao]at this
  rw[Xe _ (by simp[LF]) Z,X4,X4,eq_comm,Q3]at this
  exact this.resolve_left k
 obtain⟨r1,r2,Y⟩:=anR (by simp[LF]) h6 h7
 obtain⟨N,O,P,-⟩:=Mm d 0
 have D:q (ah d 0)≠0/\q (ah d 1)≠0:=by rw[Y]at r;simpa using r
 have rd:m (o,d)=0:=by simpa[Y,D,LF,T,U,V,z] using r1
 have E:SN o d q (m (o,ah d 0)/q (ah d 0)) m=m:=by
  funext ⟨i,j⟩;by_cases S:i=o
  · subst S;rcases (Mm d j).2.2.2 with rfl | rfl | rfl
    .simp[SN,rd]
    .simp[SN,N,D.1]
    .have :=D.1;simp[SN,O,P];field_simp;linear_combination -r2
  .simp[SN,S]
 have x0:=anA B (hF _ f) (hG _ f _ f) r (by rw[E];exact hF m hm) (by rw[E];exact hG m hm _ K)
  (by rw[E];exact hG m hm _ f) (?_) (?_)
 .rw[<- E];rcases (Mm d t).2.2.2 with rfl | rfl | rfl<;>simp[SN,x0,N,O,P]
 · rw[E];have :=aa6 (LF c d o (-1)) (single d 1) m
   rw[(P3 _ _ K m hm).2,X (single d 1) (ah d 0) (by simp[Q4,(Mm d 0).1])]at this
   linear_combination -this /2
 · rw[E];have :=aa6 (LF c d o 1) q m
   rw[(P3 _ _ f m hm).2,X (LF c d o 1) o (by simp[LF])]at this;linear_combination -this /2
set_option maxHeartbeats 0 in
def anF {c:Fq} (b:c.val<2) {o a:Ft} {q} {z y:cq}
 (s:z a=0) (p:z (ah a 0)≠0) (r:z (ah a 1)≠0)
 (n:y o=0) (l:y (ah o 0)≠0) (m:y (ah o 1)≠0)
 (j:Nv q)
 (d:dotProduct (eh c) (bj (single o 1) z)=0) (e:dotProduct (eh c) (bj y q)=0)
 (f:dotProduct (bj y q) ((lj c).mulVec (bj y q))=0)
 (g:dotProduct (bj (single o 1) z) ((lj c).mulVec (bj y q))=0)
 (h: ∑ i,oj y i* ∑ k,bj (single o 1) z (i,k)*oj q k=0):False:=by
 rcases I7 c b with rfl | rfl<;>simp +decide [bj,lj,LN,mulVec,dotProduct,S6,S9,Bm,rR,bn]at * <;>fin_cases o,a<;>
  simp +decide [bj,oj,eh,Q4,Bm,rR,bn,ah,S9]at * <;>grind
def anG {a:Ft} {φ z q v:cq} (b:∀ i,φ i≠0) (h:z a=0) (f:z (ah a 0)≠0)
 (g:z (ah a 1)≠0) (c:∀ i,q i≠0) (hv:v a=0)
 (d:v (ah a 0)*z (ah a 1)+ v (ah a 1)*z (ah a 0)=0) (e:v (ah a 0)≠0)
 (A: ∑ s,φ s* ∑ l,j1 q s l*q l=0) (B: ∑ s,φ s* ∑ l,j1 z s l*q l=0): ∑ k,oj q k*v k≠0:=by
 have :=b 0;have :=b 1;have :=b 2;have :=c 0;have :=c 1;have :=c 2;fin_cases a<;>simp[oj,j1,ah,R1]at * <;>grind
def anC {a:Ft} {z q v:cq} (r:cq) (m:z a=0) (h:z (ah a 0)≠0) (j:z (ah a 1)≠0)
 (b:∀ i,q i≠0) (hv:v a=0)
 (c:v (ah a 0)*z (ah a 1)+ v (ah a 1)*z (ah a 0)=0) (d:v (ah a 0)≠0)
 (e: ∑ k,r k*oj q k=0) (f: ∑ k,r k* ∑ l,j1 q k l*v l=0)
 (g: ∑ k,r k* ∑ l,j1 q k l*z l=0) (t:Ft):r t=0:=by
 have :=b 0;have :=b 1;have :=b 2;fin_cases a,t<;>simp[oj,j1,ah,R1]at * <;>grind
def anE (c:Fq) (l:c.val<2) M (H:gH c M) (j o b:Ft) (z y q u v:cq) (hR:bj (single j 1) z∈M)
 (zo:z b=0) (s:z (ah b 0)≠0) (zb:z (ah b 1)≠0) (a:bj y q∈M) (d:y o=0)
 (i:y (ah o 0)≠0) (yb:y (ah o 1)≠0) (D:Nv q)
 (hv:v b=0) (x:v (ah b 0)*z (ah b 1)+ v (ah b 1)*z (ah b 0)=0) (Zo:v (ah b 0)≠0)
 (n:∀ m∈M,Qf u v m=0) (J:u o≠0\/y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0)≠0):
 False:=by
 obtain⟨K,p,f,r⟩:=H;have P3:=gP3 r;by_cases g:j=o
 · subst g
   exact anF l zo s zb d i yb D (p _ hR) (p _ a) (f _ a _ a) (f _ hR _ a) (P3 y q a _ hR)
 have C:(single j 1:cq) o=0:=by simp[Q4,Ne.symm g]
 obtain⟨-,-,E,-⟩:=Mm o 0
 have cj:y (ah o 0)*(single j 1:cq) (ah o 1)+ y (ah o 1)*(single j 1:cq) (ah o 0)≠0:=by
  rcases (Mm o j).2.2.2 with h | h | h
  .exact absurd h g
  .subst h;simpa[Q4,E] using yb
  .subst h;simpa[Q4,E.symm] using i
 have A:=f _ a _ a;rw[aa5 c q q d d]at A;have B:=f _ hR _ a;rw[aa5 c z q C d]at B
 have w:=(Q3.1 A).resolve_left (by intro h;apply mul_ne_zero i yb;linear_combination h/2)
 have B':=(Q3.1 B).resolve_left (by intro h;apply cj;linear_combination h)
 have F:=adD (SM c o) (YP l o) D w;have L:=anG (YP l o) zo s zb F hv x Zo w B'
 have G:u o=0:=by
  have :=n _ a;rw[adB,Xd u d]at this;simpa[i,yb,L] using this
 have k:y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0)≠0:=J.resolve_left (by simp[G])
 have Q:∀ m∈M,Qf (single j 1) z m=0:=λm hm=> by
  have :=aa6 (single j 1) z m;rw[r _ (M.add_mem hm hR),r _ (M.sub_mem hm hR)]at this
  have e:(single j 1:cq) 0*(single j 1:cq) 1*(single j 1:cq) 2=0:=by
   fin_cases j<;>simp
  rw[e]at this;linear_combination -this /2
 refine ahu l K p f o λm hm t=> anC (λt=> m (o,t)) zo s zb F hv x Zo ?_ ?_ ?_ t
 .have :=P3 y q a m hm;rw[Xd _ d]at this;simpa[i,yb] using this
 · have :=Vg y q u v m
   rw[n _ (M.add_mem a hm),n _ a,n _ hm,Xe y d G]at this;simpa[k] using this
 · have :=Vg y q (single j 1) z m
   rw[Q _ (M.add_mem a hm),Q _ a,Q _ hm,Xe y d C]at this;simpa[cj] using this
def anH {a:Ft} {w y} {z q:cq} (e:z a=0) (c:z (ah a 0)≠0) (d:z (ah a 1)≠0)
 (b:q a≠0) (h: ∑ i,oj w i* ∑ k,bj y q (i,k)*oj z k=0): ∑ k,y k*oj w k=0:=by
 fin_cases a<;>simp[bj,oj,ah,R1]at * <;>grind
lemma ahv {o:Ft} {z q v:cq} (f:z o=0) (d:z (ah o 0)≠0) (e:z (ah o 1)≠0)
 (a:∀ i,q i≠0) (hv:v o=0)
 (b:v (ah o 0)*z (ah o 1)+ v (ah o 1)*z (ah o 0)=0) (c:v (ah o 0)≠0)
 (h: ∑ k,z k*oj q k=0): ∑ k,oj q k*v k≠0:=by
 have :=a 0;have :=a 1;have :=a 2;fin_cases o<;>simp[oj,ah,R1]at * <;>grind
def anI {o:Ft} {z q y:cq} (c:z o=0) (a:∀ i,q i≠0) (b:y o=0)
 (h: ∑ k,z k* ∑ l,j1 q k l*y l=0):z (ah o 0)*y (ah o 1)+ z (ah o 1)*y (ah o 0)=0:=by
 have :=a 0;have :=a 1;have :=a 2;fin_cases o<;>simp[j1,ah,R1]at * <;>grind
def anK (c:Fq) (D:c.val<2) (M:Submodule ℂ B9)
 (hG:∀ m∈M,∀ R∈M,dotProduct m ((lj c).mulVec R)=0) (O:∀ m∈M,p3 m=0) (o a:Ft)
 (w z y q u v s b:cq) (d:bj w z∈M) (f:z a=0) (i:z (ah a 0)≠0) (zb:z (ah a 1)≠0)
 (Q:Nv w) (dm:bj y q∈M) (yo:y o=0)
 (g:y (ah o 0)≠0) (yb:y (ah o 1)≠0) (P:Nv q)
 (hv:v a=0) (H:v (ah a 0)*z (ah a 1)+ v (ah a 1)*z (ah a 0)=0) (K:v (ah a 0)≠0)
 (E:s o=0) (n:s (ah o 0)*y (ah o 1)+ s (ah o 1)*y (ah o 0)=0) (J:s (ah o 0)≠0)
 (L:∀ m∈M,Qf u v m=0) (N:∀ m∈M,Qf s b m=0) (p:∀ m∈M,Qf u b m+ Qf s v m=0)
 (G:u o≠0\/y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0)≠0)
 (C:b a≠0\/z (ah a 0)*b (ah a 1)+ z (ah a 1)*b (ah a 0)≠0):False:=by
 have P3:=gP3 O;have A:=hG _ d _ d;rw[ahn c w w f f]at A
 have t:=adD (λr=> SM c r a) (λr=> YP D r a) Q
  ((Q3.1 A).resolve_left (by intro h;apply mul_ne_zero i zb;linear_combination h/2))
 have B:=hG _ dm _ dm;rw[aa5 c q q yo yo]at B;have q0:=adD (SM c o) (YP D o) P
  ((Q3.1 B).resolve_left (by intro h;apply mul_ne_zero g yb;linear_combination h/2))
 have T: ∑ k,z k*oj q k=0:=by
  have :=P3 y q dm _ d;rw[Xd _ yo]at this;simp only[bj,X8,<- Ao]at this;simpa[g,yb,t o] using this
 have S:=anH f i zb (q0 a) (P3 w z d _ dm)
 have F:u o=0:=by
  have :=L _ dm;rw[adB,Xd u yo]at this;simpa[g,yb,ahv f i zb q0 hv H K T] using this
 have x:b a=0:=by
  have :=N _ d;rw[adB,Xd b f]at this;simpa[i,zb,ahv yo g yb t E n J S] using this
 have k:y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0)≠0:=G.resolve_left (by simp[F])
 have e:=Vg y q s v (bj w z)
 rw[Xe y yo E,show y (ah o 0)*s (ah o 1)+ y (ah o 1)*s (ah o 0)=0 by linear_combination n,V6]at e
 have :=Vg y q u b (bj w z);rw[Xe y yo F]at this
 have h0:(y (ah o 0)*u (ah o 1)+ y (ah o 1)*u (ah o 0))* ∑ j,bj w z (o,j)* ∑ l,j1 q j l*b l=0:=by
  linear_combination -this - e+ p _ (M.add_mem dm d)- p _ dm- p _ d
 simp only[bj,X8,<- Ao]at h0
 exact C.resolve_left (by simp[x]) (anI f q0 x (by simpa[k,t o] using h0))
def MO (a b:cq):cq:= ![a 1*b 2- a 2*b 1,a 2*b 0- a 0*b 2,a 0*b 1- a 1*b 0]
lemma Rj {a} {j:Ft} {m:B9}:dotProduct (bj a (single j 1)) m= ∑ r,a r*m (r,j):=by
 simp[dotProduct,bj,S6,Q4]
lemma adC {a:cq} {j:Ft} {m:B9}:dotProduct (bj (single j 1) a) m= ∑ r,a r*m (j,r):=by
 simp[dotProduct,bj,S6,Q4]
def Yp {M:Submodule ℂ B9} (L:(cq)->B9) (b:∀ (t:ℂ) a,L (t•a)=t•L a) (f g:cq) {a:cq}
 {j:Ft} (c: ∑ r,a r*f r=0) (d: ∑ r,a r*g r=0) (e:a j≠0) (h:L a∈M):L (MO f g)∈M:=by
 rw[R1]at c d
 have k:a j•MO f g=MO f g j•a:=by funext i;fin_cases i,j<;>simp[MO]<;>grind
 exact (Bg M e).1 (by rw[<- b,k,b];exact M.smul_mem _ h)
def aa7 {M:Submodule ℂ B9} (c:3≤ finrank ℂ M) (p q:Ft× Ft):
 ∃ n∈M,n≠0/\n p=0/\n q=0:=by
 let φ:B9→ₗ[ℂ] (Fin 2->ℂ):=LinearMap.pi ![LinearMap.proj p,LinearMap.proj q];have h:=dx M φ;have b:=Z7 (M.map φ);rw[As]at b;obtain⟨n,hn,a⟩:=Bt (p:=M ⊓ ker φ)
  (λe=> by rw[e,V3]at h;omega)
 have e:=Am.1 (U1.1 hn).2
 exact⟨n,(U1.1 hn).1,a,by simpa[φ] using congrFun e 0,by simpa[φ] using congrFun e 1⟩
def Ue {M:Submodule ℂ B9} (d:∀ m∈M,p3 m=0) {a b:cq} (hb:a 0*a 1*a 2*(b 0*b 1*b 2)=0)
 (h:bj a b∈M) (m:B9) (c:m∈M):Qf a b m=0:=by
 have e:=aa6 a b m;rw[d _ (M.add_mem c h),d _ (M.sub_mem c h)]at e;linear_combination -e/2-6*hb
lemma Ug {j:Ft}:(single j 1:cq) 0*(single j 1:cq) 1*(single j 1:cq) 2=0:=by
 fin_cases j<;>simp
set_option maxHeartbeats 0 in
def akl {c:Fq} {d k o:Ft}
 (q:c=0/\d=0/\k=1\/c=1/\(d=0/\k=1\/d=1/\k=0\/d=1/\k=2)) {n:B9} {W Y:cq}
 (m:∀ i,Y i=MO (λr=> eh c (r,k)) (single o 1) i)
 (f:∀ i,W i=MO (λr=> eh c (r,d)) (λr=>(lj c).mulVec (bj Y (single k 1)) (r,d)) i)
 (h1:dotProduct (eh c) n=0) (h4:dotProduct n ((lj c).mulVec n)=0) (l:p3 n=0)
 (g: ∑ r,W r*(lj c).mulVec n (r,d)=0) (h: ∑ r,Y r*(lj c).mulVec n (r,k)=0)
 (a:Qf W (single d 1) n=0) (b:Qf Y (single k 1) n=0)
 (e: ∑ i,(∑ t,j1 Y i t*W t)* ∑ j,n (i,j)* ∑ s,j1 (single k 1) j s*(single d 1:cq) s=0)
 (A:n (0,d)=0) (B:n (ah o 0,k)=0) (p:Ft× Ft):n p=0:=by
 rcases q with⟨rfl,rfl,rfl⟩ | ⟨rfl,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩<;>
  simp +decide [eh,lj,LN,Bm,rR,bn,mulVec,dotProduct,S6,S9,p3,Qf,ah,
   j1,Q4,MO,bj,U3]at h1 h4 l g a A h b e f<;>
  fin_cases o<;>simp +decide [MO,eh,rR,bn,Q4,ah,U3]at m B<;>
  obtain⟨x,y,z⟩:=m<;>simp only[x,y,z]at h b e f<;>obtain⟨u,v,w⟩:=f<;>
  simp only[u,v,w]at g a e<;>
  (have C:n (2,0)=0:=(by grind (ringSteps:=5000));have D:n (2,1)=0:=(by grind (ringSteps:=5000));
   have E:n (2,2)=0:=(by grind (ringSteps:=5000));clear h4 a b l;rcases p with⟨i,j⟩;
   fin_cases i,j<;>grind)
def K6 (a:Ft->Ft):B9→ₗ[ℂ] B9 where
 toFun m p:=m (a p.1,a p.2)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
abbrev Xa (c:Fq) (a:Ft->Ft): Prop :=
 c=0/\(a= ![1,0,2]\/a= ![2,1,0]\/a= ![0,2,1])\/c=1/\a= ![0,2,1]
set_option maxHeartbeats 0 in
lemma aa4 {c τ} (h:Xa c τ):(∀ i,τ (τ i)=i)/\ ∀ m a:B9,
 dotProduct (eh c) (K6 τ m)=dotProduct (eh c) m/\p3 (K6 τ m)=p3 m/\
 dotProduct (K6 τ m) ((lj c).mulVec (K6 τ a))=dotProduct m ((lj c).mulVec a):=by
 rcases h with⟨rfl,rfl | rfl | rfl⟩ | ⟨rfl,rfl⟩<;>refine⟨by decide,λm a=>⟨?_,?_,?_⟩⟩<;>
  simp +decide [K6,eh,lj,LN,Bm,rR,bn,p3,dotProduct,mulVec,S6,
   S9]<;>ring
def aa3 (c:Fq) (d k o:Ft): Prop := ∀ M:Submodule ℂ B9,3≤ finrank ℂ M->
 (∀ m∈M,dotProduct (eh c) m=0)->(∀ m∈M,∀ a∈M,dotProduct m ((lj c).mulVec a)=0)->(∀ m∈M,p3 m=0)->
 ∀ w y:cq,bj w (single d 1)∈M->w≠0->bj y (single k 1)∈M->y≠0->y o=0->False
def akk c τ (l:Xa c τ) (d k o:Ft) (H:aa3 c (τ d) (τ k) (τ o)):
 aa3 c d k o:=by
 obtain⟨hi,hv⟩:=aa4 l;intro M r s t hp w y u hw dm z B
 have inj:Function.Injective (K6 τ):=λa b e=> funext λp=> by
  simpa[K6,hi] using congrFun e (τ p.1,τ p.2)
 have g:∀ m∈M.map (K6 τ),∃ A∈M,K6 τ A=m:=λm hm=> Af.1 hm
 have Tr:∀ (a:cq) j,K6 τ (bj a (single j 1))=bj (a∘ τ) (single (τ j) 1):=λa j=> by
  have e:∀ x,(τ x=j↔x= τ j):=λx=>⟨λh=> by rw[<- h,hi],λh=> by rw[h,hi]⟩
  funext p;simp[K6,bj,Q4,e]
 have nz:∀ a:cq,a≠0->a∘ τ≠0:=λa v e=> v (funext λi=> by simpa[hi] using congrFun e (τ i))
 refine H (M.map (K6 τ)) (by rw[<- Y3 (equivMapOfInjective _ inj M)];exact r)
  (λm hm=> ?_) (λm hm f n=> ?_) (λm hm=> ?_) (w∘ τ) (y∘ τ) (Tr w d ▸ S8 u) (nz w hw)
  (Tr y k ▸ S8 dm) (nz y z) (by simp[hi,B])
 .obtain⟨m,h,rfl⟩:=g m hm;rw[(hv m m).1];exact s m h
 .obtain⟨m,h,rfl⟩:=g m hm;obtain⟨f,q,rfl⟩:=g f n;rw[(hv m f).2.2];exact t m h f q
 .obtain⟨m,h,rfl⟩:=g m hm;rw[(hv m m).2.1];exact hp m h
def akj (c:Fq) (d k o:Ft)
 (u:c=0/\d=0/\k=1\/c=1/\(d=0/\k=1\/d=1/\k=0\/d=1/\k=2)):aa3 c d k o:=by
 intro M e g f hp w y h v dm hy z
 have hL:∀ (b:Ft) (t:ℂ) a,bj (t•a) (single b 1)=t•bj a (single b 1):=λb t a=> by
  funext p;simp[bj,X8]
 obtain⟨i,s⟩:=Ap.1 hy
 set Y:=MO (λr=> eh c (r,k)) (single o 1)
 have hY:bj Y (single k 1)∈M:=Yp (λa=> bj a (single k 1)) (hL k) (λr=> eh c (r,k))
  (single o 1) (by have :=g _ dm;rwa[Ah,Rj]at this)
  (by simp[Q4,z]) s dm
 obtain⟨j,hj⟩:=Ap.1 v
 set W:=MO (λr=> eh c (r,d)) (λr=>(lj c).mulVec (bj Y (single k 1)) (r,d))
 have q:bj W (single d 1)∈M:=Yp (λa=> bj a (single d 1)) (hL d) (λr=> eh c (r,d))
  (λr=>(lj c).mulVec (bj Y (single k 1)) (r,d)) (by have :=g _ h;rwa[Ah,Rj]at this)
  (by have :=f _ h _ hY;rwa[Rj]at this) hj h
 obtain⟨n,hn,x,A,B⟩:=aa7 e (0,d) (ah o 0,k)
 have Q:=Ue hp (by rw[Ug];ring) q
 have m:=Vg Y (single k 1) W (single d 1) n;rw[Q _ (M.add_mem hY hn),Q _ hY,Q _ hn]at m;have l:=f _ q _ hn;have e:=f _ hY _ hn;rw[Rj]at l e
 exact x (funext λp=> akl u (λ_=> rfl) (λ_=> rfl) (g n hn) (f n hn n hn) (hp n hn)
  l e (Q n hn) (Ue hp (by rw[Ug];ring) hY n hn) (by linear_combination -m) A B p)
lemma anx {c:Fq} (i:c.val<2) {M} (H:gH c M) {d k:Ft} (o:Ft) (a:k≠d) {w y} (h:bj w (single d 1)∈M)
 (l:w≠0) (b:bj y (single k 1)∈M) (n:y o=0) (m:y (ah o 0)≠0):False:=by
 obtain⟨h3,f,g,j⟩:=H
 refine (?_:aa3 c d k o) M h3 f g j w y h l b (λe=> m (by rw[e];rfl)) n
 have B:=akj c;have T:=akk c;rcases I7 c i with rfl | rfl<;>fin_cases d,k<;>(try exact absurd rfl a)<;>
  first
  | exact B _ _ o (by decide)
  | exact T ![1,0,2] (by decide) _ _ o (B _ _ _ (by decide))
  | exact T ![2,1,0] (by decide) _ _ o (B _ _ _ (by decide))
  | exact T ![0,2,1] (by decide) _ _ o (B _ _ _ (by decide))
  | exact T ![1,0,2] (by decide) _ _ o (T ![0,2,1] (by decide) _ _ _ (B _ _ _ (by decide)))
  | exact T ![2,1,0] (by decide) _ _ o (T ![0,2,1] (by decide) _ _ _ (B _ _ _ (by decide)))
set_option maxHeartbeats 0 in
def akm {c:Fq} (C:c.val<2) {j k o o':Ft} {n:B9} {V Y:cq}
 (hV:∀ i,V i=MO (λs=> eh c (j,s)) (single o 1) i) (q:∀ i,Y i=MO (λr=> eh c (r,k)) (single o' 1) i)
 (d: ∑ s,V s*(lj c).mulVec (bj Y (single k 1)) (j,s)=0)
 (z:dotProduct (eh c) n=0) (A:dotProduct n ((lj c).mulVec n)=0) (B:p3 n=0)
 (e: ∑ s,V s*(lj c).mulVec n (j,s)=0) (f: ∑ r,Y r*(lj c).mulVec n (r,k)=0)
 (g:Qf (single j 1) V n=0) (h:Qf Y (single k 1) n=0)
 (m: ∑ i,(∑ t,j1 (single j 1) i t*Y t)* ∑ l,n (i,l)* ∑ s,j1 V l s*(single k 1:cq) s=0)
 (D:n (j,if ah o 0=k then ah o 1 else ah o 0)=0) (E:n (if ah o' 0=j then ah o' 1 else ah o' 0,k)=0)
 (p:Ft× Ft):n p=0:=by
 rcases I7 c C with rfl | rfl<;>simp +decide [eh,lj,LN,Bm,rR,bn,mulVec,dotProduct,
  S6,S9,p3]at z A B d e f<;>
  fin_cases j,k<;>simp +decide [lj,LN,Bm,rR,bn,mulVec,dotProduct,S6,
  S9,Qf,ah,j1,Q4,bj]at d e f g h m<;>
  fin_cases o,o'<;>simp +decide [MO,eh,rR,bn,Q4,ah,U3]at hV q D E<;>
  obtain⟨v0,u,v⟩:=hV<;>obtain⟨w,x,y⟩:=q<;>simp only[v0,u,v,w,x,y]at d<;>norm_num at d<;>
  simp only[v0,u,v,w,x,y]at e f g h m<;>rcases p with⟨a,b⟩<;>fin_cases a,b<;>
  grind (ringSteps:=5000)
def anD {c:Fq} (hc:c.val<2) {M} (H:gH c M) {j k:Ft} (o o':Ft) {y} {z:cq} (q:bj (single j 1) z∈M) (A:z o=0)
 (x:z (ah o 0)≠0) (C:z (ah o 1)≠0) (h:bj y (single k 1)∈M) (u:y o'=0) (ya:y (ah o' 0)≠0)
 (B:y (ah o' 1)≠0):False:=by
 obtain⟨h3,e,d,g⟩:=H
 set V:=MO (λs=> eh c (j,s)) (single o 1)
 have b:bj (single j 1) V∈M:=Yp (λa=> bj (single j 1) a) (λt a=> by funext p;simp[bj];ring)
  (λs=> eh c (j,s)) (single o 1) (by have :=e _ q;rwa[Ah,adC]at this)
  (by simp[Q4,A]) x q
 set Y:=MO (λr=> eh c (r,k)) (single o' 1)
 have f:bj Y (single k 1)∈M:=Yp (λa=> bj a (single k 1)) (λt a=> by funext p;simp[bj,X8])
  (λr=> eh c (r,k)) (single o' 1) (by have :=e _ h;rwa[Ah,Rj]at this)
  (by simp[Q4,u]) ya h
 have m:=d _ b _ f;rw[adC]at m;obtain⟨n,hn,n0,v,w⟩:=aa7 h3 (j,if ah o 0=k then ah o 1 else ah o 0)
  (if ah o' 0=j then ah o' 1 else ah o' 0,k)
 have Q:=Ue g (by rw[Ug];ring) f
 have l:=Vg (single j 1) V Y (single k 1) n;rw[Q _ (M.add_mem b hn),Q _ b,Q _ hn]at l;have i:=d _ b _ hn;have h3:=d _ f _ hn;rw[adC]at i;rw[Rj]at h3
 exact n0 (funext λp=> akm hc (λ_=> rfl) (λ_=> rfl) m (e n hn) (d n hn n hn) (g n hn)
  i h3 (Ue g (by rw[Ug];ring) b n hn) (Q n hn) (by linear_combination -l) v w p)
set_option maxHeartbeats 0 in
def gkl {c:Fq} (hc:c.val<2) {d:Ft} {n:B9} (hn:n≠0) (e:dotProduct (eh c) n=0)
 (f:dotProduct n ((lj c).mulVec n)=0) (g:p3 n=0)
 (A:MO (λr=> eh c (r,d)) (λr=>(lj c).mulVec n (r,d))=0)
 (B:MO (λr=> eh c (r,d)) (λr=> Qf (single r 1) (single d 1) n)=0)
 (h:n (0,d)=0) (z2:n (1,d)=0):False:=by
 have a:=congrFun A 0;have b:=congrFun A 1;have A2:=congrFun A 2;have B0:=congrFun B 0;have B1:=congrFun B 1;have B2:=congrFun B 2;clear A B;apply hn;rcases Y8 (n (2,d)) 0 with z3 | z3<;>rcases I7 c hc with rfl | rfl<;>simp +decide [eh,lj,LN,Bm,rR,bn,mulVec,dotProduct,S6,S9]at e f g a b A2 B0 B1 B2 h z2 z3<;>fin_cases d<;>
 simp +decide [eh,Bm,rR,bn,S9,p3,Qf,ah,Q4,MO]at e f g a b A2 B0 B1 B2 h z2 z3<;>
 (try simp only[h,z2,z3,T6,V6,S0,Y0]at e f g a b A2 B0 B1 B2)<;>funext ⟨i,j⟩<;>fin_cases i,j<;>(try simp only[Fin.reduceFinMk,Fin.isValue,W0])<;>
 grind (ringSteps:=4000)
def gX {a b f g:cq} (c: ∑ r,a r*f r=0) (d: ∑ r,a r*g r=0) (n: ∑ r,b r*f r=0)
 (o: ∑ r,b r*g r=0) (q:a≠0) (s:∀ t:ℂ,b≠t•a):MO f g=0:=by
 have k:∀ x:cq,∑ r,x r*f r=0-> ∑ r,x r*g r=0-> ∀ j i,x j*MO f g i=MO f g j*x i:=by
  intro x c d j i;rw[R1]at c d;fin_cases i,j<;>simp[MO]<;>grind
 by_contra p;obtain⟨j,e⟩:=Ap.1 p;simp only[W0]at e
 have h:a j≠0:=λm=> q (funext λi=> by
  have :=k a c d j i;rw[m,V6]at this;simpa[e] using this.symm)
 exact s (b j/a j) (funext λi=> by
  have e1:=k a c d j i;have l:=k b n o j i;simp only[Q6,Q5];rw[Be,Bw h];apply mul_left_cancel₀ e;linear_combination (-a j)*l+ b j*e1)
def ahp {c:Fq} (hc:c.val<2) {M} (H:gH c M) (d:Ft) {w w'} (s:bj w (single d 1)∈M)
 (p:bj w' (single d 1)∈M) (hi:∀ t:ℂ,w'≠t•w) (j:w≠0):False:=by
 obtain⟨q,hF,g,i⟩:=H;obtain⟨n,hn,u,v,x⟩:=aa7 q (0,d) (1,d);have f:∀ a,bj a (single d 1)∈M-> ∑ r,a r*eh c (r,d)=0/\ ∑ r,a r*(lj c).mulVec n (r,d)=0/\
   ∑ r,a r*Qf (single r 1) (single d 1) n=0:=λa h=> by
  refine⟨?_,by rw[<- Rj];exact g _ h n hn,?_⟩
  .rw[<- Rj,Ah];exact hF _ h
  · have e:=Ue i (by rw[Ug,T6]) h n hn
    generalize (single d 1:cq)=y at e ⊢
    simp only[Qf,R1,Q4]at e ⊢;simp at e ⊢;linear_combination e
 obtain⟨b,k,l⟩:=f w s;obtain⟨b1,m,o⟩:=f w' p;exact gkl hc u (hF n hn) (g n hn n hn) (i n hn) (gX b k b1 m j hi) (gX b l b1 o j hi) v x
def Qp:B9→ₗ[ℂ] B9 where
 toFun m p:=m (p.2,p.1)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
set_option maxHeartbeats 0 in
lemma adA {c:Fq} (a:c.val<2) m m':dotProduct (eh c) (Qp m)=dotProduct (eh c) m/\
 dotProduct (Qp m) ((lj c).mulVec (Qp m'))=dotProduct m ((lj c).mulVec m'):=by
 constructor<;>rcases I7 c a with rfl | rfl<;>simp +decide [Qp,eh,lj,LN,dotProduct,mulVec,
  S6,S9,Bm,rR,bn]<;>ring
lemma gqt {u y:cq} {a:ℂ} {M:B9}:Qf u (a•y) M=a*Qf u y M:=by
 simp only[Qf,R1,Q6,Q5];ring
lemma gTq {u y:cq} {m}:Qf u y (Qp m)=Qf y u m:=by
 simp only[Qf,Qp,Ac,Ad,ah,R1];simp;ring
lemma XK {a b}:Qp (bj a b)=bj b a:=by funext p;simp[Qp,bj,Az]
def gHf {c M} (f:B9→ₗ[ℂ] B9) (i:∀ m,f (f m)=m) (hv:∀ m a:B9,
 dotProduct (eh c) (f m)=dotProduct (eh c) m/\p3 (f m)=p3 m/\
 dotProduct (f m) ((lj c).mulVec (f a))=dotProduct m ((lj c).mulVec a)) (H:gH c M):gH c (M.map f):=by
 obtain⟨d,e,g,j⟩:=H
 refine⟨by rw[<- Y3 (equivMapOfInjective _ (Function.LeftInverse.injective i) M)];exact d,
  ?_,?_,?_⟩
 .rintro _ ⟨m,h,rfl⟩;rw[(hv m m).1];exact e m h
 .rintro _ ⟨m,h,rfl⟩ _ ⟨a,b,rfl⟩;rw[(hv m a).2.2];exact g m h a b
 .rintro _ ⟨m,h,rfl⟩;rw[(hv m m).2.1];exact j m h
def gHT {c:Fq} (a:c.val<2) {M} (H:gH c M):gH c (M.map Qp):=
 gHf Qp (λ_=> rfl) (λm b=>⟨(adA a m m).1,by simp[p3,Qp];ring,(adA a m b).2⟩) H
def gHP {c τ} (a:Xa c τ) {M} (H:gH c M):gH c (M.map (K6 τ)):=
 gHf _ (λm=> funext λp=> by simp[K6,(aa4 a).1]) (aa4 a).2 H
def QJ (o:Ft) (s:Fin 2) (a b c:ℂ):cq:=λr=> if r=o then a else if r=ah o s then b else c
abbrev ahf (c:Fq) (d i:Ft): Prop :=
 c=0/\d=0/\(i=0\/i=1)\/c=1/\(d=0/\i=0\/d=1/\i=1\/d=0/\i=1\/d=1/\i=2)
def e2A (c:Fq) (d i:Ft) (w v z y:cq) (n:B9): Prop :=
 let R:=bj w (single d 1);let a:=bj (single i 1) v;let G:=λm b=> dotProduct m ((lj c).mulVec b)
 dotProduct (eh c) R=0/\dotProduct (eh c) a=0/\G R a=0/\Qf z y (R+ a)=0/\dotProduct (eh c) n=0/\
 G R n=0/\G a n=0/\Qf w (single d 1) (a+ n)=0/\Qf (single i 1) y (R+ n)=0/\Qf z (single d 1) (a+ n)=0/\
 G n n=0/\Qf w (single d 1) n=0/\Qf (single i 1) v n=0/\Qf (single i 1) (single d 1) n=0/\
 Qf z (single d 1) n=0/\Qf (single i 1) y n=0
set_option maxHeartbeats 0 in
def aki {c d i s t}
 (o:ahf c d i)
 {w0 w2 v0 v2 zi z1 z2 yd y1 y2 x0 x2 x4 x5 x6 x7 x8}
 (H:e2A c d i (QJ i s w0 1 w2) (QJ d t v0 1 v2) (QJ i s zi z1 z2) (QJ d t yd y1 y2)
  (λp=> QJ i s (QJ d t x0 0 x2 p.2) (QJ d t 0 x4 x5 p.2) (QJ d t x6 x7 x8 p.2) p.1))
 (C:s=0\/w2=0) (pt:t=0\/v2=0) (r:z1≠0\/z2≠0) (q:y1≠0\/y2≠0)
 (hn:x0≠0\/x2≠0\/x4≠0\/x5≠0\/x6≠0\/x7≠0\/x8≠0):False:=by
 simp[e2A,eh,lj,LN,rR,mulVec,dotProduct,S6,R1,Qf,ah,bj]at H;rcases o with⟨rfl,rfl,rfl | rfl⟩ | ⟨rfl,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩<;>fin_cases s,t<;>
  simp[QJ,Bm,bn,ah,Q4,T0]at H<;>
  obtain⟨w,x,y,n,z,A,B,b,k,e,v,a,u,j,f,g⟩:=H<;>
  (rcases Q3.1 (show (v2*y1+y2)*(w2*z1+z2)=0 by linear_combination n) with hP | hP
   · obtain rfl :=Aq hP
     have l:y1≠0:=by rintro rfl;simp at q
     obtain rfl :=Aq
      ((Q3.1 (show y1*(w2*x5+x8)=0 by linear_combination (y1*(b-a)+k-g)/2)).resolve_left l)
     rcases Q3.1 ((Q3.1 (show y1*(v2*(w2*x4+x7))=0 by linear_combination (y1*(b-a)-k+g)/2)).resolve_left l)
      with hv | hv
     .grind
     obtain rfl :=Aq hv
     have :w2*x4*x5=0:=(by linear_combination -j/2)
     simp at this;rcases this with (h | h) | h<;>grind
   · obtain rfl :=Aq hP
     have m:z1≠0:=by rintro rfl;simp at r
     obtain rfl :=Aq
      ((Q3.1 (show z1*(v2*x7+x8)=0 by linear_combination (z1*(b-a)+e-f)/2)).resolve_left m)
     rcases Q3.1 ((Q3.1 (show z1*(w2*(v2*x4+x5))=0 by linear_combination (z1*(b-a)-e+f)/2)).resolve_left m)
      with hw | hw
     .grind
     obtain rfl :=Aq hw
     have :v2*x4*x7=0:=(by linear_combination -j/2)
     simp at this;rcases this with (h | h) | h<;>grind)
lemma YQ o s (u:cq):u=QJ o s (u o) (u (ah o s)) (u (ah o (s+1))):=by
 funext r;fin_cases o,s,r<;>rfl
lemma ahr o d s t (n:B9):n=λp=> QJ o s
 (QJ d t (n (o,d)) (n (o,ah d t)) (n (o,ah d (t+1))) p.2)
 (QJ d t (n (ah o s,d)) (n (ah o s,ah d t)) (n (ah o s,ah d (t+1))) p.2)
 (QJ d t (n (ah o (s+1),d)) (n (ah o (s+1),ah d t)) (n (ah o (s+1),ah d (t+1))) p.2) p.1:=by
 funext ⟨r,k⟩;rw[congrFun (YQ d t (λk=> n (r,k))) k];fin_cases o,s,r<;>rfl
def W9 (c:Fq) (d i:Ft): Prop := ∀ M,gH c M-> ∀ w v z a:cq,bj w (single d 1)∈M->w≠0->
 bj (single i 1) v∈M->v≠0->(∀ t:ℂ,z≠t•single i 1)->(∀ t:ℂ,a≠t•single d 1)->
 (∀ m∈M,Qf z a m=0/\Qf z (single d 1) m=0/\Qf (single i 1) a m=0/\
  Qf (single i 1) (single d 1) m=0)->False
def ahd {c:Fq} (hc:c.val<2) (o d:Ft) {w:cq} (e:w≠0)
 (h:dotProduct (eh c) (bj w (single d 1))=0):∃ s:Fin 2,w (ah o s)≠0/\(s=0\/w (ah o (s+1))=0):=by
 by_cases a:w (ah o 0)=0
 · refine⟨1,λb=> e ?_,.inr a⟩;funext r
   rcases I7 c hc with rfl | rfl<;>fin_cases o,d,r<;>
    simp[eh,rR,bn,dotProduct,bj,S6,R1,ah,Q4]at a b h ⊢ <;>grind
 exact⟨0,a,.inl rfl⟩
def ahe {o:Ft} (s:Fin 2) {z:cq} (a:∀ t:ℂ,z≠t•single o 1):
 z (ah o s)≠0\/z (ah o (s+1))≠0:=by
 by_contra h;push_neg at h;apply a (z o);funext r;fin_cases o,s,r<;>simp[ah,Q4]at h ⊢ <;>grind
def Ve {c:Fq} (j:c.val<2) d i (F:ahf c d i:=by decide):W9 c d i:=by
 intro M ⟨E,g,hG,k⟩ w v z r m J l hv K u hq;obtain⟨s,G,N⟩:=ahd j i d J (g _ m)
 obtain⟨t,ht,P⟩:=ahd j d i hv (by rw[<- XK,(adA j _ 0).1];exact g _ l)
 obtain⟨f,a,Zp,O⟩:∃ f:cq,bj f (single d 1)∈M/\f (ah i s)=1/\(s=0\/f (ah i (s+1))=0):=
  ⟨(w (ah i s))⁻¹•w,by convert M.smul_mem (w (ah i s))⁻¹ m using 1;funext p;simp[bj,X8],
   by simp[V9 G],N.imp_right λh=> by simp[h]⟩
 obtain⟨e,b,Wn,Q⟩:∃ e:cq,bj (single i 1) e∈M/\e (ah d t)=1/\(t=0\/e (ah d (t+1))=0):=
  ⟨(v (ah d t))⁻¹•v,by convert M.smul_mem (v (ah d t))⁻¹ l using 1;funext p;simp[bj,mul_left_comm],
   by simp[V9 ht],P.imp_right λh=> by simp[h]⟩
 obtain⟨n,hn,L,o,q⟩:=aa7 E (ah i s,d) (i,ah d t);have H:e2A c d i f e z r n:=⟨g _ a,g _ b,hG _ a _ b,(hq _ (M.add_mem a b)).1,g _ hn,
  hG _ a _ hn,hG _ b _ hn,Ue k (by rw[Ug];ring) a _ (M.add_mem b hn),
  (hq _ (M.add_mem a hn)).2.2.1,(hq _ (M.add_mem b hn)).2.1,hG _ hn _ hn,Ue k (by rw[Ug];ring) a _ hn,
  Ue k (by rw[Ug];ring) b _ hn,(hq _ hn).2.2.2,(hq _ hn).2.1,(hq _ hn).2.2.1⟩
 rw[YQ i s f,Zp,YQ d t e,Wn,YQ i s z,YQ d t r,ahr i d s t n,o,q]at H;refine aki F H O Q (ahe s K) (ahe t u) ?_;by_contra h;push_neg at h;obtain⟨x,y,a3,A,B,C,D⟩:=h
 exact L (by rw[ahr i d s t n,o,q,x,y,a3,A,B,C,D];funext p;simp[QJ])
def anv {c:Fq} (j:c.val<2) d i (H:W9 c i d):W9 c d i:=by
 intro M g w v z o hR hw dm hv n KR l;refine H _ (gHT j g) v w o z (XK ▸ S8 dm) hv (XK ▸ S8 hR) hw
  KR n λm k=> ?_
 obtain⟨m,h,rfl⟩:=k;simp only[gTq];obtain⟨a,b,e,f⟩:=l m h;exact⟨a,e,b,f⟩
def Xc {c} τ (d i:Ft) (H:W9 c (τ d) (τ i)) (Iq:Xa c τ:=by decide):W9 c d i:=by
 have hi:=(aa4 Iq).1;intro M n w v z g o s l k hz KR r
 have e:∀ j x,(τ x=j↔x= τ j):=λj x=>⟨λh=> by rw[<- h,hi],λh=> by rw[h,hi]⟩
 have S:∀ j,(single j 1:cq)∘ τ=single (τ j) 1:=λj=> funext λx=> by simp[Q4,e]
 have I:∀ a:cq,(a∘ τ)∘ τ=a:=λa=> funext λx=> by simp[hi]
 have f:∀ a:cq,a≠0->a∘ τ≠0:=λa p h=> p (by rw[<- I a,h];rfl)
 have Q:∀ a b m,Qf a b (K6 τ m)=Qf (a∘ τ) (b∘ τ) m:=λa b m=> by
  rcases Iq with⟨-,rfl | rfl | rfl⟩ | ⟨-,rfl⟩<;>simp[Qf,K6,R1,ah]<;>ring
 refine H _ (gHP Iq n) (w∘ τ) (v∘ τ) (z∘ τ) (g∘ τ) ?_ (f w s) ?_ (f v k)
  (λt h=> hz t ?_) (λt h=> KR t ?_) (λm q=> ?_)
 .rw[<- S];exact S8 o
 .rw[<- S];exact S8 l
 .rw[<- I z,h,<- S];funext x;simp[hi]
 .rw[<- I g,h,<- S];funext x;simp[hi]
 .obtain⟨m,h,rfl⟩:=q;simp only[Q,<- S,I];exact r m h
lemma anw {c:Fq} (a:c.val<2) {M} (H:gH c M) {d i:Ft} {w} {v:cq} (z b:cq)
 (g:bj w (single d 1)∈M) (j:w≠0) (f:bj (single i 1) v∈M) (hv:v≠0)
 (k:∀ t:ℂ,z≠t•single i 1) (e:∀ t:ℂ,b≠t•single d 1)
 (h:∀ m∈M,Qf z b m=0/\Qf z (single d 1) m=0/\Qf (single i 1) b m=0/\
  Qf (single i 1) (single d 1) m=0):False:=by
 refine (?_:W9 c d i) M H w v z b g j f hv k e h;have T:=anv a;rcases I7 c a with rfl | rfl<;>fin_cases d,i<;>
  first
  | exact Ve a _ _
  | exact T _ _ (Ve a _ _)
  | exact Xc ![1,0,2] _ _ (Ve a _ _)
  | exact Xc ![2,1,0] _ _ (Ve a _ _)
  | exact Xc ![0,2,1] _ _ (Ve a _ _)
  | exact T _ _ (Xc ![0,2,1] _ _ (Ve a _ _))
  | exact Xc ![1,0,2] _ _ (Xc ![0,2,1] _ _ (Ve a _ _))
def YO (w:cq): Prop :=w 0=1\/w 0=0/\w 1=1\/w 0=0/\w 1=0/\w 2=1
set_option maxHeartbeats 0 in
def anQ (c:Fq) (l:c.val<2) (d i:Ft) (w v:cq) (m:B9) (a:ℂ)
 (h:(lj c).mulVec m=a•eh c+ bj (λr=> j1 w r i) (λj=> j1 v j d))
 (e:dotProduct (eh c) m=0) (f:dotProduct (bj (λr=> j1 w r i) (λj=> j1 v j d)) m=0)
 (hq:Qf w (single d 1) m=0) (OW:Qf (single i 1) v m=0)
 (hf:dotProduct (eh c) (bj w (single d 1))=0) (b:dotProduct (eh c) (bj (single i 1) v)=0)
 (hw:YO w) (hv:YO v):False:=by
 unfold YO at hw hv
 have g:=λp=> congrFun h p
 clear h;rcases I7 c l with rfl | rfl<;>simp +decide [LN,lj,eh,mulVec,dotProduct,S6,S9,Bm,rR,bn,Prod.forall,U3]at g e f hq OW hf b<;>fin_cases d,i<;>
  simp +decide [eh,bj,j1,Qf,ah,S9,Bm,rR,bn,Prod.forall,U3,Q4]at g e f hq OW hf b<;>
  rcases hw with hw | ⟨hw,k⟩ | ⟨hw,k,o⟩<;>rcases hv with hv | ⟨hv,hv'⟩ | ⟨hv,hv',n⟩<;>grind
def gS (L:Sq) (c:Fq) (X:Mt): Prop :=(∀ t∈L,p4 (Bm+ t)=65)/\finrank ℂ L=6/\c.val<2/\
 finrank ℂ (L.map (af 0))=2/\finrank ℂ (L.map (Kl c))=2/\X∈L/\X (0,c)≠0
def e2d {L:Sq} (n:finrank ℂ L=6) {c:Fq}
  (k:finrank ℂ (L.map (af 0))=2) (o:finrank ℂ (L.map (Kl c))=2) {X:Mt} (a:X∈L)
  (b:X (0,c)≠0):finrank ℂ ↥(Ar L 0)=4/\finrank ℂ ↥(iu L c)=4/\
   3≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c):=by
 have i:=dx L (af 0);have j:=dx L (Kl c)
 have e:finrank ℂ ↥(Ar L 0)=4:=by unfold Ar;omega
 have f:finrank ℂ ↥(iu L c)=4:=by unfold iu;omega
 have d:Ar L 0 ⊔ iu L c< L:=by
  refine Z9 (sup_le inf_le_left inf_le_left) (λh=> b ?_)
  rw[<- h]at a;obtain⟨Y,g,Z,hZ,rfl⟩:=V0.1 a;rw[R5,((ei L 0 Y).1 g).2 c,((ti L c Z).1 hZ).2 0,S0]
 have l:=Dc d;have m:=Bb (Ar L 0) (iu L c)
 exact⟨e,f,by omega⟩
def apk:∀ c o:Fq,c≠o->cr c o 0≠cr c o 1/\
    ((cr (cr c o 0) (cr c o 1) 0=c/\cr (cr c o 0) (cr c o 1) 1=o)\/
     (cr (cr c o 0) (cr c o 1) 0=o/\cr (cr c o 0) (cr c o 1) 1=c)):=by decide
def aeI {L:Sq} (n:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (l:finrank ℂ (L.map (af 0))=2)
  {X:Mt} (e:X∈L) (b:X (0,c)≠0):∃ o:Fq,c≠o/\ ∃ Y∈L ⊔ span ℂ {Bm},
   Y∉ L/\Y (0,c)=0/\Y (0,o)=0:=by
 have p:af 0 X≠0:=λh=> b (by simpa[bu] using congrFun h c)
 have g:¬ (L.map (af 0)≤ span ℂ {af 0 X}):=λh=> by
  have :=W1 h;rw[Ab p,l]at this;omega
 obtain⟨v,hv,hvn⟩:=Set.not_subset.1 g;obtain⟨a,d,rfl⟩:=hv
 obtain⟨o,i⟩:∃ o,X (0,c)*a (0,o)- a (0,c)*X (0,o)≠0:=by
  by_contra f;push_neg at f
  exact hvn (X3.2 ⟨a (0,c)/X (0,c),by
   funext j;simp only[bu,Q6,Q5];rw[Be,div_eq_iff b];linear_combination -(f j)⟩)
 refine⟨o,λh=> i (by rw[h];ring),(a (0,c)*Bm (0,o)- Bm (0,c)*a (0,o))•X+
  (Bm (0,c)*X (0,o)- X (0,c)*Bm (0,o))•a+(X (0,c)*a (0,o)- a (0,c)*X (0,o))•Bm,
  V0.2 ⟨_,L.add_mem (L.smul_mem _ e) (L.smul_mem _ d),_,
   T4 _ _ (Ay Bm),rfl⟩,λk=> ?_,?_,?_⟩
 .have m:(X (0,c)*a (0,o)- a (0,c)*X (0,o))•Bm∈L:=by
   have :=L.sub_mem k (L.add_mem (L.smul_mem (a (0,c)*Bm (0,o)- Bm (0,c)*a (0,o)) e)
    (L.smul_mem (Bm (0,c)*X (0,o)- X (0,c)*Bm (0,o)) d))
   simpa using this
  exact Pe L n ((L.smul_mem_iff i).1 m)
 .simp only[R5,Q6,Q5];ring
 .simp only[R5,Q6,Q5];ring
def ahc {L:Sq} (l:∀ t∈L,p4 (Bm+ t)=65) (j:finrank ℂ ↥(Ar L 0)=4) {c o:Fq}
  (f:c≠o) {Y:Mt} (n:Y∈L ⊔ span ℂ {Bm}) (g:Y∉ L) (u:Y (0,c)=0)
  (v:Y (0,o)=0):∃ Z∈Ar L 0 ⊓ iu L c,Z≠0/\(∀ i,Z (i,o)=0)/\
   ∀ i,Y (0,cr c o 0)*Z (i,cr c o 1)+ Y (0,cr c o 1)*Z (i,cr c o 0)=0:=by
 obtain⟨r,a⟩:=apk c o f
 have p:Y (0,cr (cr c o 0) (cr c o 1) 0)=0:=by rcases a with⟨e,-⟩ | ⟨e,-⟩<;>rw[e]<;>assumption
 have q:Y (0,cr (cr c o 0) (cr c o 1) 1)=0:=by rcases a with⟨-,e⟩ | ⟨-,e⟩<;>rw[e]<;>assumption
 obtain⟨Z,b,h,Wj⟩:=B2L L l j _ _ r _ _ Y n g p q rfl rfl;have d:=((ei L 0 Z).1 b).2
 have k:∀ i k,Z (i,cr (cr c o 0) (cr c o 1) k)=0:=by
  intro i k;rcases Ck i with rfl | ⟨m,rfl⟩
  .exact d _
  .fin_cases k
   .simpa[sl] using congrFun Wj (m,0)
   .simpa[sl] using congrFun Wj (m,1)
 have s:∀ i,Z (i,c)=0:=λi=> by rcases a with⟨e,-⟩ | ⟨-,e⟩<;>rw[<- e]<;>exact k i _
 have ko:∀ i,Z (i,o)=0:=λi=> by rcases a with⟨-,e⟩ | ⟨e,-⟩<;>rw[<- e]<;>exact k i _
 refine⟨Z,U1.2 ⟨b,(ti L c Z).2 ⟨((ei L 0 Z).1 b).1,s⟩⟩,h,ko,λi=> ?_⟩
 rcases Ck i with rfl | ⟨m,rfl⟩
 .rw[d,d];ring
 .simpa[sl] using congrFun Wj (m,2)
def glv {N:Sq} (hN:∀ t∈N,p4 (Bm+ t)=65) {c:Fq} (hc:c.val<2)
 (hr:∀ X∈N,∀ j,X (0,j)=0) (g:∀ X∈N,∀ i,X (i,c)=0):
 finrank ℂ ↥(N.map (dq c))=finrank ℂ N/\(∀ m∈N.map (dq c),dotProduct (eh c) m=0/\p3 m=0)/\
 ∀ m∈N.map (dq c),∀ m'∈N.map (dq c),dotProduct m ((lj c).mulVec m')=0:=by
 have E:=λn (hn:n∈N) d (Ni:d∈N)=> anL hc (hr n hn) (g n hn) (hr d Ni) (g d Ni)
 have l:Bm (0,c)≠0:=by rcases I7 c hc with rfl | rfl<;>simp[Bm]
 refine⟨?_,λm h=> ?_,λm h m' k=> ?_⟩
 · have :=LinearMap.finrank_range_of_inj (f:=(dq c).comp N.subtype) (λa b e=> Subtype.ext (Bn.1
    (ahl hc (hr _ (N.sub_mem a.2 b.2)) (g _ (N.sub_mem a.2 b.2)) (by rw[V8];exact Bn.2 e))))
   rwa[LinearMap.range_comp,Submodule.range_subtype]at this
 · obtain⟨n,hn,rfl⟩:=h
   obtain⟨a,b,-⟩:=E n hn n hn
   rw[hN n hn,hN _ (N.neg_mem hn),hN _ (N.smul_mem (2:ℂ) hn),hN _ (N.smul_mem (-2:ℂ) hn)]at a b
   exact⟨by linear_combination -a/12,
    (Q3.1 (by linear_combination -b/12:Bm (0,c)*p3 (dq c n)=0)).resolve_left l⟩
 · obtain⟨n,hn,rfl⟩:=h;obtain⟨d,Ni,rfl⟩:=k
   obtain⟨-,-,e⟩:=E n hn d Ni
   rw[hN _ (N.add_mem hn Ni),hN _ (N.sub_mem hn Ni),hN _ (N.add_mem (N.neg_mem hn) Ni),
    hN _ (N.sub_mem (N.neg_mem hn) Ni)]at e
   linear_combination -e/4
def gy (o:Ft) (a b:ℂ):cq:=λj=> if j=ah o 0 then a else if j=ah o 1 then b else 0
def gsh (B:B9) (o:Ft) {y0 c:ℂ} (h:y0≠0\/c≠0) (e:∀ r,B (r,o)=0)
 (d:∀ r,y0*B (r,ah o 1)+ c*B (r,ah o 0)=0):∃ w,B=bj w (gy o y0 (-c)):=by
 rcases h with h | h
 · refine⟨λr=> B (r,ah o 0)/y0,funext λ⟨r,j⟩=> ?_⟩
   have a:=e r;have b:=d r
   fin_cases o,j<;>simp[bj,gy,ah]at a b ⊢ <;>first | exact a | (field_simp;linear_combination b) | field_simp
 · refine⟨λr=> -B (r,ah o 1)/c,funext λ⟨r,j⟩=> ?_⟩
   have a:=e r;have b:=d r
   fin_cases o,j<;>simp[bj,gy,ah]at a b ⊢ <;>first | exact a | (field_simp;linear_combination b) | field_simp
def gob {c:Fq} (a:c.val<2) {o:Fq} (b:c≠o):∃ d:Ft,bn c (rR d)=o:=by
 rcases I7 c a with rfl | rfl<;>fin_cases o<;>simp at b<;>decide
def got {c:Fq} (b:c.val<2) (a:Ft):(∀ k,cr c (bn c (rR a)) k=bn c (rR (ah a k)))/\
 ∀ j,j=c\/j=bn c (rR a)\/j=bn c (rR (ah a 0))\/j=bn c (rR (ah a 1)):=by
 rcases I7 c b with rfl | rfl<;>fin_cases a<;>decide
lemma gtw {c:Fq} (a:c.val<2) {X:Mt}:dq c (ig c X)=λp=> dq c X (p.2,p.1):=by
 funext ⟨r,s⟩;simp only[dq,Ac,Ad,Ip c a,(oq c a).2.2.2]
def gtm {c:Fq} (a:c.val<2) (L:Sq) (Z:Mt)
 (g:Z∈Ar (L.map (ig c)) 0 ⊓ iu (L.map (ig c)) c):ig c Z∈Ar L 0 ⊓ iu L c:=by
 obtain⟨e,f⟩:=U1.1 g;obtain⟨d,hr⟩:=(ei _ 0 Z).1 e;obtain⟨-,h⟩:=(ti _ c Z).1 f
 have b:ig c Z∈L:=by rw[<- Nj c a L];exact S8 d
 refine U1.2 ⟨(ei L 0 _).2 ⟨b,λj=> ?_⟩,(ti L c _).2 ⟨b,λi=> ?_⟩⟩
 .rw[Ip c a,(oq c a).1];exact h _
 .rw[Ip c a,(oq c a).2.1];exact hr _
def grs {L:Sq} (f:∀ t∈L,p4 (Bm+ t)=65) (XR:finrank ℂ ↥(Ar L 0)=4) {c:Fq}
 (d:c.val<2) {a:Ft} {Y:Mt} (i:Y∈L ⊔ span ℂ {Bm}) (I2:Y∉ L) (n:Y (0,c)=0)
 (q:Y (0,bn c (rR a))=0):(Y (0,bn c (rR (ah a 0)))≠0\/Y (0,bn c (rR (ah a 1)))≠0)/\
 ∃ w,w≠0/\bj w (gy a (Y (0,bn c (rR (ah a 0)))) (-Y (0,bn c (rR (ah a 1)))))∈
  (Ar L 0 ⊓ iu L c).map (dq c):=by
 obtain⟨b,s⟩:=got d a
 have hy:Y (0,bn c (rR (ah a 0)))≠0\/Y (0,bn c (rR (ah a 1)))≠0:=by
  by_contra h;push_neg at h;obtain⟨X,hX,m,u,rfl⟩:=V0.1 i;obtain⟨l,rfl⟩:=X3.1 u
  have hl:l≠0:=λh=> I2 (by rw[h,T9,S0];exact hX)
  have e:=Ud L f X hX l
  rw[Bo,Pb 0 _ (λj=> by rcases s j with h' | h' | h' | h'<;>rw[h']<;>simp_all)]at e
  exact hl (by simpa using e.symm)
 refine⟨hy,?_⟩;obtain⟨Z,hZ,KX,v,x⟩:=ahc f XR (sg3 c d a).1.symm i I2 n q
 obtain⟨w,k⟩:=gsh (dq c Z) a hy (λr=> v _) (λr=> by
  have :=x (rR r);rw[b 0,b 1]at this;simp only[dq,Ac,Ad];linear_combination this)
 have g:=U1.1 hZ
 have o:w≠0:=by
  rintro rfl
  exact KX (ahl d ((ei L 0 Z).1 g.1).2 ((ti L c Z).1 g.2).2 (by rw[k];funext p;simp[bj]))
 exact⟨w,o,by rw[<- k];exact S8 hZ⟩
def o8 (c:Fq):Mt→ₗ[ℂ] (cq) where
 toFun X i:=X (rR i,c)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def I8 (c:Fq):Mt→ₗ[ℂ] (cq) where
 toFun X j:=X (0,bn c (rR j))
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma gqa {u a y:cq} {M:B9}:Qf (u+ a) y M=Qf u y M+ Qf a y M:=by
 simp only[Qf,R1,R5];ring
lemma gqy {u y a:cq} {M:B9}:Qf u (y+ a) M=Qf u y M+ Qf u a M:=by
 simp only[Qf,R1,R5];ring
lemma gqs {a:ℂ} {u y:cq} {M:B9}:Qf (a•u) y M=a*Qf u y M:=by
 simp only[Qf,R1,Q6,Q5];ring
def gbx {c:Fq} (a:c.val<2) (X:Mt) (h:X (0,c)=0):p4 X=Qf (o8 c X) (I8 c X) (dq c X):=by
 rcases I7 c a with rfl | rfl<;>
  simp[p4,Qf,ah,rR,dq,o8,I8,bn,R1,T0,h]<;>ring
def gq0 {L:Sq} (p:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (hc:c.val<2)
 {V:Mt} (q:V∈L ⊔ span ℂ {Bm}) (k:V (0,c)=0) {n:Mt} (hn:n∈Ar L 0 ⊓ iu L c):
 Qf (o8 c V) (I8 c V) (dq c n)=0:=by
 obtain⟨X,r,m,v,b⟩:=V0.1 q;obtain⟨l,rfl⟩:=X3.1 v;obtain⟨h1,o⟩:=U1.1 hn;obtain⟨hnL,f⟩:=(ei L 0 n).1 h1;obtain⟨-,u⟩:=(ti L c n).1 o
 have d:o8 c n=0:=funext λi=> u _
 have g:I8 c n=0:=funext λj=> f _
 have a:∀ s:ℂ,Qf (o8 c V) (I8 c V) (dq c V+ s•dq c n)=65*l^4:=by
  intro s
  have e:=gbx hc (V+ s•n) (by simp[k,f])
  rw[show V+ s•n=l•Bm+(X+ s•n) by rw[<- b];abel,Ud L p _ (L.add_mem r (L.smul_mem s hnL)) l,
   show l•Bm+(X+ s•n)=V+ s•n by rw[<- b];abel]at e
  rw[S4,S4,S4,S5,S5,S5,d,g,Z6,S0,S0]at e;exact e.symm
 have k1:=a 1;have k2:=a (-1);have h:=a 0;rw[aeg]at k1 k2 h;linear_combination (k1+ k2-2*h)/2
def gq1 {L:Sq} (W:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (x:c.val<2)
 (Z:finrank ℂ (L.map (Kl c))=2) {d:Mt} (E:d∈Ar L 0) (N:o8 c d≠0)
 (a b:Mt) (m:a∈L ⊔ span ℂ {Bm}) (k:a (0,c)=0) (o:b∈L ⊔ span ℂ {Bm})
 (l:b (0,c)=0) {n:Mt} (hn:n∈Ar L 0 ⊓ iu L c):Qf (o8 c a) (I8 c b) (dq c n)=0:=by
 obtain⟨p,LQ⟩:=(ei L 0 d).1 E
 have G:I8 c d=0:=funext λj=> LQ _
 have hS:=λ(V:Mt) (X:V∈L ⊔ span ℂ {Bm}) (M:V (0,c)=0)=> gq0 W x X M hn
 have q:=hS a m k;have a2:=hS b o l
 have s:=hS (a+ b) (V7 _ m o) (by simp[k,l])
 have z1:=hS (d+ a) (V7 _ (Y9 p) m) (by simp[LQ,k])
 have u:=hS (d+ b) (V7 _ (Y9 p) o) (by simp[LQ,l])
 simp only[S4,G,Y0]at s z1 u;rw[gqa,gqy,gqy]at s;rw[gqa]at z1;rw[gqa]at u;obtain⟨O,H,m1,z,e1⟩:=V0.1 m;obtain⟨C,rfl⟩:=X3.1 z;obtain⟨P,J,m2,F,w⟩:=V0.1 o;obtain⟨D,rfl⟩:=X3.1 F;let v:Ft-> ↥(L.map (Kl c)):= ![⟨Kl c O,S8 H⟩,⟨Kl c P,S8 J⟩,
  ⟨Kl c d,S8 p⟩]
 have hv:¬ LinearIndependent ℂ v:=λh=> by have :=h.fintype_card_le_finrank;simp[Z]at this
 obtain⟨g,Y,i,hi⟩:=Fintype.not_linearIndependent_iff.1 hv
 have hg':=λr=> congrFun (congrArg Subtype.val Y) r
 simp[R1,v,Nt]at hg'
 have U:Bm (0,c)≠0:=by rcases I7 c x with rfl | rfl<;>simp[Bm]
 have T:g 0*C+ g 1*D=0:=by
  have :=hg' 0;rw[LQ]at this;have e:=congrFun e1 (0,c);have f:=congrFun w (0,c);simp only[R5,Q6,Q5,k,l]at e f
  exact (Q3.1 (by linear_combination -this + g 0*e+ g 1*f:
   (g 0*C+ g 1*D)*Bm (0,c)=0)).resolve_right U
 have A:g 0•o8 c a+ g 1•o8 c b=(-g 2)•o8 c d:=by
  funext r;have :=hg' (rR r);have e:=congrFun e1 (rR r,c);have f:=congrFun w (rR r,c);simp only[R5,Q6,Q5,o8,Ac,Ad]at e f ⊢;linear_combination this - g 0*e- g 1*f+ Bm (rR r,c)*T
 have B:∀ y,g 0*Qf (o8 c a) y (dq c n)+ g 1*Qf (o8 c b) y (dq c n)=
   -g 2*Qf (o8 c d) y (dq c n):=λy=> by
  rw[<- gqs,<- gqs,<- gqa,A,gqs]
 have Q:=B (I8 c a);have R:=B (I8 c b);by_cases h:g 0=0
 · have K:g 1≠0:=λS=> by
    have :=A;simp[h,S]at this;rcases this with h3 | h3
    .fin_cases i<;>simp_all
    .exact N h3
   have :Qf (o8 c b) (I8 c a) (dq c n)=0:=
    (Q3.1 (by linear_combination Q- g 2*(z1- q)- g 0*q:g 1*_=0)).resolve_left K
   linear_combination s- q- a2- this
 .exact (Q3.1 (by linear_combination R- g 2*(u- a2)- g 1*a2:g 0*_=0)).resolve_left h
def gnv {L:Sq} (hL:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (g:c.val<2) {V:Mt}
 (f:V∈L ⊔ span ℂ {Bm}) (b:V∉ L) (a:V (0,c)=0):o8 c V≠0/\I8 c V≠0:=by
 obtain⟨X,d,m,hm,rfl⟩:=V0.1 f;obtain⟨l,rfl⟩:=X3.1 hm
 have hl:l≠0:=λh=> b (by rw[h,T9,S0];exact d)
 have e:=Ud L hL X d l;rw[Bo]at e
 have k:=λh:p4 (X+ l•Bm)=0=> hl (by simpa[h] using e.symm)
 obtain⟨hot,hj⟩:=got g 0;constructor<;>intro h
 · apply k;rw[<- afB];refine Pb c _ λi=> ?_
   rw[Mw];fin_cases i
   .exact a
   .simpa[o8,rR] using congrFun h 0
   .simpa[o8,rR] using congrFun h 1
   .simpa[o8,rR] using congrFun h 2
 · apply k;refine Pb 0 _ λj=> ?_
   rcases hj j with e1 | e1 | e1 | e1<;>rw[e1]
   .exact a
   .simpa[I8] using congrFun h 0
   .simpa[I8] using congrFun h (ah 0 0)
   .simpa[I8] using congrFun h (ah 0 1)
def gZ {L} {c:Fq} (e:c.val<2) (g:finrank ℂ ↥(Ar L 0)=4) (hC:finrank ℂ ↥(iu L c)=4)
 (d:finrank ℂ ↥(Ar L 0 ⊓ iu L c)=3):(∃ Z∈Ar L 0,o8 c Z≠0)/\ ∃ Z∈iu L c,I8 c Z≠0:=by
 constructor
 · obtain⟨Z,a,b⟩:=At (Z9 inf_le_left λh=> by rw[h]at d;omega)
   refine⟨Z,a,λh=> b (U1.2 ⟨a,(ti L c Z).2 ⟨((ei L 0 Z).1 a).1,λi=> ?_⟩⟩)⟩
   fin_cases i
   .exact ((ei L 0 Z).1 a).2 c
   .simpa[o8,rR] using congrFun h 0
   .simpa[o8,rR] using congrFun h 1
   .simpa[o8,rR] using congrFun h 2
 · obtain⟨Z,a,b⟩:=At (Z9 By λh=> by rw[h]at d;omega)
   refine⟨Z,a,λh=> b (U1.2 ⟨(ei L 0 Z).2 ⟨((ti L c Z).1 a).1,λj=> ?_⟩,a⟩)⟩
   obtain⟨-,f⟩:=got e 0
   rcases f j with e1 | e1 | e1 | e1<;>rw[e1]
   .exact ((ti L c Z).1 a).2 0
   .simpa[I8] using congrFun h 0
   .simpa[I8] using congrFun h (ah 0 0)
   .simpa[I8] using congrFun h (ah 0 1)
def gcx {L:Sq} (hL:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (o:c.val<2)
 (N:finrank ℂ (L.map (Kl c))=2) {d Ki f Yc:Mt} (q:d∈Ar L 0) (w:o8 c d≠0)
 (B:Ki∈iu L c) (A:I8 c Ki≠0) (i:f∈L ⊔ span ℂ {Bm}) (u:f∉ L) (l:f (0,c)=0)
 (g:Yc∈L ⊔ span ℂ {Bm}) (s:Yc∉ L) (k:Yc (0,c)=0):
 (∀ t:ℂ,o8 c d≠t•o8 c Yc)/\(∀ t:ℂ,I8 c Ki≠t•I8 c f)/\ ∀ m∈(Ar L 0 ⊓ iu L c).map (dq c),
 Qf (o8 c d) (I8 c Ki) m=0/\Qf (o8 c d) (I8 c f) m=0/\Qf (o8 c Yc) (I8 c Ki) m=0/\
 Qf (o8 c Yc) (I8 c f) m=0:=by
 obtain⟨p,LQ⟩:=(ei L 0 d).1 q;obtain⟨r,j⟩:=(ti L c Ki).1 B;have x:d∈L ⊔ span ℂ {Bm}:=Y9 p;have y:Ki∈L ⊔ span ℂ {Bm}:=Y9 r;have sub:∀ (Z Y:Mt) (t:ℂ),Z∈L->Y∈L ⊔ span ℂ {Bm}->Y∉ L->t≠0->
   Z- t•Y∈L ⊔ span ℂ {Bm}/\Z- t•Y∉ L:=λZ Y t v K z ht=>
  ⟨Ai _ (Y9 v) (T4 _ t K),λh=> z (by
   have :=L.sub_mem v h;rw[sub_sub_cancel]at this;exact (L.smul_mem_iff ht).1 this)⟩
 refine⟨λt e=> ?_,λt e=> ?_,λm M=> ?_⟩
 · rcases Y8 t 0 with rfl | ht
   .exact w (by simpa using e)
   · obtain⟨a,b⟩:=sub d Yc t p g s ht
     exact (gnv hL o a b (by simp[LQ,k])).1 (by rw[V8,S5,e,Aj])
 · rcases Y8 t 0 with rfl | ht
   .exact A (by simpa using e)
   · obtain⟨a,b⟩:=sub Ki f t r i u ht
     exact (gnv hL o a b (by simp[j,l])).2 (by rw[V8,S5,e,Aj])
 · obtain⟨n,hn,rfl⟩:=M
   have G:=λC D H E J F=> gq1 hL o N q w C D H E J F hn
   exact⟨G _ _ x (LQ c) y (j 0),G _ _ x (LQ c) i l,G _ _ g k y (j 0),G _ _ g k i l⟩
def gso {L:Sq} (g:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (o:Fq) {X:Mt} (e:X∈L) (f:X (0,c)≠0)
 {a:Mt} (b:a∈L) (d:a (0,c)=0) (auQ:a (0,o)≠0):
 ∃ Y∈L ⊔ span ℂ {Bm},Y∉ L/\Y (0,c)=0/\Y (0,o)=0:=by
 refine⟨(-Bm (0,c))•X+((Bm (0,c)*X (0,o)- X (0,c)*Bm (0,o))/a (0,o))•a+ X (0,c)•Bm,
  V0.2 ⟨_,L.add_mem (L.smul_mem _ e) (L.smul_mem _ b),_,
   T4 _ _ (Ay Bm),rfl⟩,λh=> ?_,?_,?_⟩
 · apply Pe L g
   have :=L.sub_mem h (L.add_mem (L.smul_mem (-Bm (0,c)) e)
    (L.smul_mem ((Bm (0,c)*X (0,o)- X (0,c)*Bm (0,o))/a (0,o)) b))
   rw[add_sub_cancel_left]at this;exact (L.smul_mem_iff f).1 this
 .simp[d];ring
 .simp only[R5,Q6,Q5];field_simp;ring
def gLp {L c X} (S:gS L c X):gS (L.map (ig c)) c (ig c X):=by
 obtain⟨f,e,a,d,h,g,b⟩:=id S
 exact⟨aaN c L f,by rw[aaM];exact e,a,by rw[UG c a];exact h,by rw[<- UG c a,Nj c a];exact d,
  S8 g,by rw[Ip c a,(oq c a).1,(oq c a).2.1];exact b⟩
lemma gtB (c:Fq):ig c Bm=Bm:=by simp[ig,afM,acf]
def gpb {L c X} (S:gS L c X)
 {b:Ft} {Y:Mt} (hY:Y∈L.map (ig c) ⊔ span ℂ {Bm}) (e:Y∉ L.map (ig c)) (g:Y (0,c)=0)
 (UW:Y (0,bn c (rR b))=0):∃ Y∈L ⊔ span ℂ {Bm},Y∉ L/\Y (0,c)=0/\Y (rR b,c)=0/\
  (Y (rR (ah b 0),c)≠0\/Y (rR (ah b 1),c)≠0)/\ ∃ v,v≠0/\
  bj (gy b (Y (rR (ah b 0),c)) (-Y (rR (ah b 1),c))) v∈(Ar L 0 ⊓ iu L c).map (dq c):=by
 obtain⟨z,y,a,x,B,A,K9⟩:=id S;obtain⟨m,l,-,k,o,p,n⟩:=gLp S;obtain⟨q,-,-⟩:=e2d l k o p n;obtain⟨u,w,t,hR⟩:=grs m q a hY e g UW;obtain⟨Z,hZ,hZe⟩:=hR;have d:∀ i j,ig c Y (i,j)=Y (bn c j,bn c i):=Ip c a Y
 refine⟨ig c Y,?_,λh=> e ?_,?_,?_,?_,w,t,?_⟩
 · have :=S8 (f:=ig c) hY
   rwa[Cb,Nj c a,Cc,Cd,gtB c]at this
 · have :=S8 (f:=ig c) h
   rwa[<- Al,show (ig c).comp (ig c)=LinearMap.id from LinearMap.ext λX=> by
    funext ⟨i,j⟩;simp only[Al,Ip c a,(oq c a).2.2.2,Ba],
    Ba]at this
 .rw[d,(oq c a).1,(oq c a).2.1];exact g
 .rw[d,(oq c a).2.1];exact UW
 .rw[d,d,(oq c a).2.1];exact u
 · rw[d,d,(oq c a).2.1]
   refine⟨ig c Z,gtm a L Z hZ,?_⟩
   rw[gtw a,hZe];funext ⟨r,s⟩;simp only[bj];ring
def gD0 (M:Submodule ℂ B9) (f e:Ft) (c d a b:ℂ) (w v:cq): Prop :=
 w≠0/\v≠0/\(c≠0\/d≠0)/\(a≠0\/b≠0)/\bj w (gy f c (-d))∈M/\bj (gy e a (-b)) v∈M/\
 ∀ t:ℂ,bj (gy e a (-b)) v≠t•bj w (gy f c (-d))
def gD (M:Submodule ℂ B9) (b a:Ft) (e f c d:ℂ) (w v z g:cq): Prop :=
 gD0 M b a e f c d w v/\(∀ t:ℂ,z≠t•gy a c d)/\(∀ t:ℂ,g≠t•gy b e f)/\ ∀ m∈M,
  Qf z g m=0/\Qf z (gy b e f) m=0/\Qf (gy a c d) g m=0/\Qf (gy a c d) (gy b e f) m=0
def gne {a:cq} (b:cq) (ha:a≠0) (c:b≠0):bj a b≠0:=λh=> by
 obtain⟨i,d⟩:=Ap.1 ha;obtain⟨j,e⟩:=Ap.1 c
 exact mul_ne_zero d e (by simpa[bj] using congrFun h (i,j))
def gy0 o (a b:ℂ) (h:a≠0\/b≠0):gy o a b≠0:=λe=> by
 have e0:=congrFun e (ah o 0);have c:=congrFun e (ah o 1);fin_cases o<;>simp[gy,ah]at e0 c<;>tauto
def gnz {o} {a b:ℂ} {z:cq} (h:a≠0\/b≠0) (e:∀ t:ℂ,z≠t•gy o a b):
 z o≠0\/gy o a (-b) (ah o 0)*z (ah o 1)+ gy o a (-b) (ah o 1)*z (ah o 0)≠0:=by
 by_contra d;push_neg at d;obtain⟨c,h1⟩:=d;rcases h with h | h
 · exact e (z (ah o 0)/a) (funext λi=> by
    fin_cases o,i<;>simp[gy,ah]at c h1 ⊢ <;>first | exact c | (field_simp;linear_combination h1) | (field_simp;linear_combination -h1) | field_simp)
 · exact e (z (ah o 1)/b) (funext λi=> by
    fin_cases o,i<;>simp[gy,ah]at c h1 ⊢ <;>first | exact c | (field_simp;linear_combination h1) | (field_simp;linear_combination -h1) | field_simp)
def ahA {M ob iy y0 y1 u0 u1 w v}
 (D:gD0 M ob iy y0 y1 u0 u1 w v):gD0 (M.map Qp) iy ob u0 u1 y0 y1 v w:=by
 obtain⟨b,hv,c,f,hR,d,hn⟩:=D
 refine⟨hv,b,f,c,XK ▸ S8 d,XK ▸ S8 hR,λt e=> ?_⟩
 have a:=congrArg Qp e;rw[S5,XK,XK]at a;rcases Y8 t 0 with rfl | ht
 .exact gne _ b (gy0 ob y0 (-y1) (by rcases c with h | h<;>simp[h])) (by simpa using a)
 .exact hn t⁻¹ (by rw[a,Ae,V9 ht,Aw])
def gDT {M ob iy y0 y1 u0 u1 w v z z'}
 (D:gD M ob iy y0 y1 u0 u1 w v z z'):gD (M.map Qp) iy ob u0 u1 y0 y1 v w z' z:=by
 obtain⟨D0,f,KR,e⟩:=D
 refine⟨ahA D0,KR,f,λm hm=> ?_⟩
 obtain⟨m,h,rfl⟩:=hm;obtain⟨a,b,c,d⟩:=e m h;simp only[gTq];exact⟨a,c,b,d⟩
lemma LP o a b:gy o a b o=0/\gy o a b (ah o 0)=a/\gy o a b (ah o 1)=b:=by
 fin_cases o<;>simp[gy,ah]
def UT ob {y0 c:ℂ} (h:y0=0\/c=0) (h':y0≠0\/c≠0):∃ d:Ft,∃ a b:ℂ,a≠0/\b≠0/\
 gy ob y0 (-c)=a•single d 1/\gy ob y0 c=b•single d 1:=by
 rcases h with rfl | rfl
 · refine⟨ah ob 1,-c,c,by simpa using h',by simpa using h',?_,?_⟩<;>funext i<;>
    fin_cases ob,i<;>simp[gy,ah]
 · refine⟨ah ob 0,y0,y0,by simpa using h',by simpa using h',?_,?_⟩<;>funext i<;>
    fin_cases ob,i<;>simp[gy,ah]
def gtp {w:cq} (d:w≠0):(∃ k,w=w k•single k 1/\w k≠0)\/
 Nv w:=by
 by_cases a:w 0=0<;>by_cases b:w 1=0<;>by_cases c:w 2=0
 .exact absurd (funext λi=> by fin_cases i<;>assumption) d
 .exact Or.inl ⟨2,funext λi=> by fin_cases i<;>simp[a,b],c⟩
 .exact Or.inl ⟨1,funext λi=> by fin_cases i<;>simp[a,c],b⟩
 .exact Or.inr (Or.inr (Or.inr ⟨b,c⟩))
 .exact Or.inl ⟨0,funext λi=> by fin_cases i<;>simp[b,c],a⟩
 .exact Or.inr (Or.inr (Or.inl ⟨a,c⟩))
 .exact Or.inr (Or.inl ⟨a,b⟩)
 .exact Or.inr (Or.inl ⟨a,b⟩)
def gw3 {w:cq} (a:w≠0):w 0≠0\/w 1≠0\/w 2≠0:=by
 by_contra h;push_neg at h;exact a (funext λi=> by fin_cases i<;>simp[h.1,h.2.1,h.2.2])
lemma Na {a} {b:cq} {t:ℂ}:bj a (t•b)=bj (t•a) b/\bj (t•a) b=t•bj a b:=by
 constructor<;>funext p<;>simp[bj]<;>ring
def gAA {c:Fq} (r:c.val<2) {M} (H:gH c M) {ob iy y0 y1 u0 u1}
 {w v z z'} (D:gD M ob iy y0 y1 u0 u1 w v z z') (t:y0=0\/y1=0) (A:u0=0\/u1=0):False:=by
 obtain⟨⟨u,hv,x,hu,g,dm,-⟩,j,KR,hq⟩:=D;obtain⟨d,a,b,q,hb,e,f⟩:=UT ob t x;obtain⟨i,B,n,ha',hb',o,p⟩:=UT iy A hu;rw[e,(Na).1]at g;rw[o,<- (Na).1]at dm;rw[f]at KR hq;rw[p]at j hq;refine anw r H z z' g (Y5 q u) dm (Y5 ha' hv)
  (λs h=> j (s/n) (by rw[h,Ae,Cq _ hb']))
  (λs h=> KR (s/b) (by rw[h,Ae,Cq _ hb])) λm hm=> ?_
 obtain⟨y,k,l,q4⟩:=hq m hm;simp only[gqt,gqs,Q3,hb,hb',false_or]at k l q4;exact⟨y,k,l,q4⟩
def gAB {c:Fq} (hc:c.val<2) {M} (H:gH c M) {ob iy y0 y1 u0 u1}
 {w v} (D:gD0 M ob iy y0 y1 u0 u1 w v) (t:y0=0\/y1=0)
 (n:u0≠0/\u1≠0/\ ∃ k,v=v k•single k 1/\v k≠0):False:=by
 obtain⟨f,hv,m,o,hR,b,hn⟩:=D;obtain⟨d,a,-,ha,-,e,-⟩:=UT ob t m;obtain⟨j,-,k,g,l⟩:=n;rw[e,(Na).1]at hR hn;rw[g,(Na).1]at b hn;obtain⟨h,i,-⟩:=LP iy u0 (-u1);by_cases hkd:k=d
 · subst hkd
   exact ahp hc H k hR b (λs e=> hn s (by rw[e,(Na).2])) (Y5 ha f)
 · exact anx hc H iy hkd hR (Y5 ha f) b (by simp[h])
    (by simp[i,l,j])
def gAC {c:Fq} (n:c.val<2) {M} (H:gH c M) {ob iy y0 y1 u0 u1}
 {w v z z'} (D:gD M ob iy y0 y1 u0 u1 w v z z') (t:y0=0\/y1=0)
 (u:u0≠0/\u1≠0/\(Nv v)):False:=by
 obtain⟨⟨r,hv,s,q,hR,dm,-⟩,hz,-,p⟩:=D;obtain⟨d,a,b,l,hb,e,e'⟩:=UT ob t s;obtain⟨i,j,k⟩:=u;rw[e,(Na).1]at hR;obtain⟨f,g,h⟩:=LP iy u0 (-u1)
 exact anz c n M H d iy _ _ v z hR (gw3 (Y5 l r)) dm f (by rw[g];exact i)
  (by rw[h];exact X9.2 j) k (λm o=> by
   have :=(p m o).2.1;rw[e',gqt]at this;exact (Q3.1 this).resolve_left hb) (gnz q hz)
def gBC {c:Fq} (r:c.val<2) {M} (H:gH c M) {ob iy y0 y1 u0 u1}
 {w v z z'} (D:gD M ob iy y0 y1 u0 u1 w v z z') (t:y0≠0/\y1≠0/\ ∃ j,w=w j•single j 1/\w j≠0)
 (B:u0≠0/\u1≠0/\(Nv v)):False:=by
 obtain⟨⟨-,-,-,u,e,n,-⟩,x,-,hq⟩:=D;obtain⟨h0,q,j,o,f⟩:=t;obtain⟨h,l,d⟩:=B;rw[o,<- (Na).1]at e;obtain⟨p,a,b⟩:=LP ob y0 (-y1);obtain⟨VY,k,i⟩:=LP iy u0 (-u1);obtain⟨y,g,A⟩:=LP ob y0 y1
 exact anE c r M H j iy ob _ _ v z (gy ob y0 y1) e (by simp[p]) (by simp[a,f,h0])
  (by simp[b,f,q]) n VY (by rw[k];exact h) (by rw[i];exact X9.2 l) d y
  (by simp[g,A,a,b];ring) (by rw[g];exact h0) (λm s=>(hq m s).2.1) (gnz u x)
def gpl (c:Fq) (hc:c.val<2) M (H:gH c M) ob iy y0 y1 u0 u1
 w v (D:gD0 M ob iy y0 y1 u0 u1 w v) (y:(y0=0\/y1=0)->(u0=0\/u1=0)->False)
 (t:(y0=0\/y1=0)\/ ∃ j,w=w j•single j 1/\w j≠0)
 (h:(u0=0\/u1=0)\/ ∃ k,v=v k•single k 1/\v k≠0):False:=by
 by_cases b:y0=0\/y1=0<;>by_cases a:u0=0\/u1=0
 .exact y b a
 .exact gAB hc H D b ⟨(X5.1 a).1,(X5.1 a).2,h.resolve_left a⟩
 · exact gAB hc (gHT hc H) (ahA D) a
    ⟨(X5.1 b).1,(X5.1 b).2,t.resolve_left b⟩
 · obtain⟨-,-,-,-,e,d,-⟩:=D
   obtain⟨u,x⟩:=X5.1 b;obtain⟨i,n⟩:=X5.1 a;obtain⟨j,p,f⟩:=t.resolve_left b
   obtain⟨k,q,g⟩:=h.resolve_left a
   rw[p,<- (Na).1]at e;rw[q,(Na).1]at d
   obtain⟨r,s,g2⟩:=LP ob y0 (-y1);obtain⟨o,m,l⟩:=LP iy u0 (-u1)
   exact anD hc H ob iy e (by simp[r]) (by simp[s,f,u]) (by simp[g2,f,x])
    d (by simp[o]) (by simp[m,g,i]) (by simp[l,g,n])
def gpk (c:Fq) (a:c.val<2) M (H:gH c M) ob iy y0 y1 u0 u1
 w v z z' (D:gD M ob iy y0 y1 u0 u1 w v z z'):False:=by
 have T:=gDT D;have j:=gHT a H;have t:=D.1.1;have hv:=D.1.2.1;by_cases f:y0=0\/y1=0<;>by_cases e:u0=0\/u1=0
 .exact gpl c a M H _ _ _ _ _ _ _ _ D.1 (gAA a H D) (.inl f) (.inl e)
 · have b:=X5.1 e;rcases gtp hv with hk | h2
   .exact gpl c a M H _ _ _ _ _ _ _ _ D.1 (gAA a H D) (.inl f) (.inr hk)
   .exact gAC a H D f ⟨b.1,b.2,h2⟩
 · have n:=X5.1 f;rcases gtp t with hk | h2
   .exact gpl c a M H _ _ _ _ _ _ _ _ D.1 (gAA a H D) (.inr hk) (.inl e)
   .exact gAC a j T e ⟨n.1,n.2,h2⟩
 · have n:=X5.1 f;have b:=X5.1 e
   rcases gtp t with hk | h2<;>rcases gtp hv with l | h
   .exact gpl c a M H _ _ _ _ _ _ _ _ D.1 (gAA a H D) (.inr hk) (.inr l)
   .exact gBC a H D ⟨n.1,n.2,hk⟩ ⟨b.1,b.2,h⟩
   .exact gBC a j T ⟨b.1,b.2,l⟩ ⟨n.1,n.2,h2⟩
   · obtain⟨⟨-,-,L,K,J,E,-⟩,N,A,g⟩:=D
     obtain⟨s,G⟩:=n;obtain⟨k,B⟩:=b
     obtain⟨F,q,r⟩:=LP ob y0 (-y1);obtain⟨C,p,o⟩:=LP iy u0 (-u1)
     obtain⟨O,x,P⟩:=LP ob y0 y1;obtain⟨u,i,y⟩:=LP iy u0 u1
     exact anK c a M H.2.2.1 H.2.2.2 iy ob w _ _ v z (gy ob y0 y1) (gy iy u0 u1) z' J F (by rw[q];exact s)
      (by rw[r];exact X9.2 G) h2 E C (by rw[p];exact k) (by rw[o];exact X9.2 B) h O
      (by simp[x,P,q,r];ring) (by rw[x];exact s) u (by simp[i,y,p,o];ring) (by rw[i];exact k)
      (λm d=>(g m d).2.1) (λm d=>(g m d).2.2.1) (λm d=> by rw[(g m d).1,(g m d).2.2.2,S0])
      (gnz K N)
      (gnz L A)
lemma gyr {c:Fq} {a:Ft} {Y:Mt} (h:Y (0,bn c (rR a))=0):
 I8 c Y=gy a (Y (0,bn c (rR (ah a 0)))) (Y (0,bn c (rR (ah a 1)))):=by
 funext j;fin_cases a,j<;>simp[I8,gy,ah]at h ⊢ <;>exact h
lemma gyc {c:Fq} {a:Ft} {Y:Mt} (h:Y (rR a,c)=0):
 o8 c Y=gy a (Y (rR (ah a 0),c)) (Y (rR (ah a 1),c)):=by
 funext j;fin_cases a,j<;>simp[o8,gy,ah]at h ⊢ <;>exact h
def gts {c:Fq} (a:c.val<2) {L:Sq} {Y:Mt} (d:Y∈L ⊔ span ℂ {Bm}) (b:Y∉ L):
 ig c Y∈L.map (ig c) ⊔ span ℂ {Bm}/\ig c Y∉ L.map (ig c):=by
 refine⟨?_,λh=> b ?_⟩
 · have :=S8 (f:=ig c) d
   rwa[Cb,Cc,Cd,gtB c]at this
 · have :=S8 (f:=ig c) h
   rwa[Nj c a,<- Al,show (ig c).comp (ig c)=LinearMap.id from LinearMap.ext λX=> by
    funext ⟨i,j⟩;simp only[Al,Ip c a,(oq c a).2.2.2,Ba],
    Ba]at this
def gZ3 {c:Fq} (k:c.val<2) {d a:Ft} {e:Fin 2} {Z:Mt} {t:ℂ} (l:t≠0) (b:∀ i,Z (i,c)=0)
 (h2:∀ j,Z (rR a,j)=0) (h3:∀ j,Z (rR (ah a (1- e)),j)=0) (f:Z (0,bn c (rR d))=0)
 (g:∀ j,Z (rR (ah a e),j)=t*Z (0,j)) (ha:Z (0,bn c (rR (ah d 0)))≠0) (hb:Z (0,bn c (rR (ah d 1)))≠0)
 (h:p4 (Bm+ Z)+ p4 (Bm- Z)=130):False:=by
 simp[p4,Bm]at h;rcases I7 c k with rfl | rfl<;>fin_cases d,a,e<;>
  simp +decide [rR,bn,ah]at b h2 h3 f g ha hb<;>simp[b,h2,h3,f,g]at h<;>grind (ringSteps:=2000)
def gcv {c:Fq} (b:c.val<2) (d a:Ft) (e:Fin 2) {A B s:Fq}
 (h:A=bn c (rR a)/\B=bn c (rR (ah a (1- e)))/\s=bn c (rR (ah a e))):
 (∀ i:Fq,i=0\/i=rR a\/i=rR (ah a e)\/i=rR (ah a (1- e)))/\
 (∀ l:Fq,l=c\/l=bn c (rR d)\/l=bn c (rR (ah d 0))\/l=bn c (rR (ah d 1)))/\A≠B/\
 (cr A B 0=c/\cr A B 1=s\/cr A B 0=s/\cr A B 1=c):=by
 obtain⟨rfl,rfl,rfl⟩:=h;rcases I7 c b with rfl | rfl<;>fin_cases d,a,e<;>decide
open Submodule in
def g1d {L:Sq} (a:finrank ℂ (L.map (af 0))=2) {c:Fq} (j k:Fq) {X V W:Mt} (f:X∈L) (b:V∈L)
 (d:W∈L) (K9:X (0,c)≠0) (hv:V (0,c)=0) (m:W (0,c)=0):V (0,j)*W (0,k)=V (0,k)*W (0,j):=by
 by_contra n
 have h:LinearIndependent ℂ ![af 0 X,af 0 V,af 0 W]:=Ax.2 λg hg=> by
  have e:=λl=> congrFun hg l;simp[R1,bu]at e
  have :=e c;have :=e j;have :=e k;intro i;fin_cases i<;>simp<;>grind
 have :=finrank_mono (span_le.2 (Cx.2 λi=> by
  fin_cases i;exacts [Bx f,Bx b,Bx d]):
   span ℂ (Set.range ![af 0 X,af 0 V,af 0 W])≤ L.map (af 0))
 rw[Bq h,a]at this;simp at this
open Submodule in
def gRI L c X (S:gS L c X)
 (d a:Ft) (b:Mt) (Mp:b∈L ⊔ span ℂ {Bm}) (LJ:b∉ L) (LA:b (0,c)=0) (Ny:b (rR a,c)=0)
 (Ld:b (rR (ah a 0),c)≠0) (OX:b (rR (ah a 1),c)≠0)
 (hI:Bm (rR (ah a 0),c)*b (rR (ah a 1),c)≠Bm (rR (ah a 1),c)*b (rR (ah a 0),c))
 (E:Mt) (D:E∈L) (F:E (0,c)=0) (G:E (rR a,c)≠0) (hEk:∀ k,E (rR (ah a k),c)=0)
 (U:∀ Z∈L,Z (0,c)=0->Z (0,bn c (rR d))=0) (Ki:Mt) (w:Ki∈iu L c)
 (QO:Ki (0,bn c (rR (ah d 0)))≠0) (Ta:Ki (0,bn c (rR (ah d 1)))≠0):False:=by
 obtain⟨s,h6,f,h0,hq,hX,V⟩:=id S;have J:∀ e:Fin 2,b (rR (ah a (1- e)),c)*Bm (rR (ah a e),c)- Bm (rR (ah a (1- e)),c)*
   b (rR (ah a e),c)≠0:=λe h=> hI (by fin_cases e<;>simp at h<;>first | linear_combination h | linear_combination -h)
 obtain⟨e,he⟩:∃ e:Fin 2,b (rR (ah a (1- e)),c)•Bm- Bm (rR (ah a (1- e)),c)•b∉ L:=by
  by_contra H;push_neg at H;apply Pe L s;refine (L.smul_mem_iff (sub_ne_zero.2 hI)).1 ?_;convert L.sub_mem (L.smul_mem (Bm (rR (ah a 0),c)) (H 0)) (L.smul_mem (Bm (rR (ah a 1),c)) (H 1)) using 1;funext q;simp;ring
 have hu:b (rR (ah a (1- e)),c)≠0:=by fin_cases e<;>simpa
 set p:=ah a (1- e);obtain⟨W,Zc⟩:∃ W:Mt,W=b (rR p,c)•Bm- Bm (rR p,c)•b-(b (rR p,c)*Bm (rR a,c)/E (rR a,c))•E:=
  ⟨_,rfl⟩
 have M:W∈L ⊔ span ℂ {Bm}:=Zc ▸ Ai _ (Ai _ (T4 _ _
  (Y2 (Y6 Bm))) (T4 _ _ Mp))
  (X7 (L.smul_mem _ D))
 have K:W∉ L:=λh=> he (by simpa[Zc] using L.add_mem h (L.smul_mem (b (rR p,c)*Bm (rR a,c)/E (rR a,c)) D))
 simp only[Bd,W8,Q6,Q5,Prod.forall]at Zc
 have x:W (0,c)≠0:=by rw[Zc,LA,F];simpa using mul_ne_zero hu (by unfold Bm;split_ifs<;>norm_num)
 have Q:W (rR (ah a e),c)≠0:=by rw[Zc,hEk,T6,X4];exact J e
 obtain⟨v,T,-,ss⟩:=oq c f;obtain⟨Ly,Lx,-,Kj,OW,Qs,O7⟩:=gLp S;obtain⟨Ul,-,-⟩:=e2d Lx Kj OW Qs O7;obtain⟨t1,t2⟩:=gts f M K;have m:=Ip c f W;obtain⟨y,z,O,hO⟩:=gcv f d a e ⟨rfl,rfl,rfl⟩;obtain⟨g,N,Y,P,hs⟩:=ahc Ly Ul O t1 t2
  (by rw[m,ss,v,Zc,Ny,T6,X4,Cq _ G,Aj])
  (by rw[m,ss,v,Zc,hEk];ring)
 have u:=W7.1 N;have A:=((ti _ _ g).1 u.2).2
 have KU:ig c g∈L:=by rw[<- Nj c f L];exact Bx ((ei _ 0 g).1 u.1).1
 have ez:=Ip c f g;set Z:=ig c g
 have n:∀ i,Z (i,c)=0:=λi=> by rw[ez,T];exact ((ei _ 0 g).1 u.1).2 _
 have B:=U _ KU (n 0)
 have C:∀ j,Z (rR (ah a e),j)=(-W (rR (ah a e),c)/W (0,c))*Z (0,j):=λj=> by
  have :=hs (bn c j);rw[Be,Bw x,ez,ez];rcases hO with⟨R,o2⟩ | ⟨R,o2⟩<;>rw[R,o2,m,m]at this<;>
   simp only[ss,v,T]at this ⊢ <;>linear_combination this
 have U0:=g1d h0 (bn c (rR (ah d 0))) (bn c (rR (ah d 1))) hX KU ((ti L c Ki).1 w).1 V
  (n 0) (((ti L c Ki).1 w).2 0)
 by_cases o:Z (0,bn c (rR (ah d 0)))=0
 · have t:Z (0,bn c (rR (ah d 1)))=0:=by rw[o,V6]at U0;exact (Q3.1 U0.symm).resolve_right QO
   have r:∀ l,Z (0,l)=0:=λl=> by rcases z l with rfl | rfl | rfl | rfl;exacts [n 0,B,o,t]
   refine Y (funext λ⟨i,j⟩=> ?_)
   have :Z (bn c j,bn c i)=0:=by
    rcases y (bn c j) with h | h | h | h<;>rw[h]
    exacts [r _,by rw[ez];exact A _,by rw[C,r,T6],by rw[ez];exact P _]
   rwa[ez,ss,ss]at this
 · exact gZ3 f (div_ne_zero (X9.2 Q) x) n (λj=> by rw[ez];exact A _)
    (λj=> by rw[ez];exact P _) B C o (λt=> o (by rw[t,V6]at U0;exact (Q3.1 U0).resolve_right Ta))
    (by rw[sub_eq_add_neg,s _ KU,s _ (L.neg_mem KU)];norm_num)
def gNH {L c X} (S:gS L c X)
 (i:3≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c)):finrank ℂ ↥(Ar L 0)=4/\gH c ((Ar L 0 ⊓ iu L c).map (dq c))/\
 finrank ℂ ((Ar L 0 ⊓ iu L c).map (dq c))=finrank ℂ ↥(Ar L 0 ⊓ iu L c):=by
 obtain⟨l,j,o,g,p,n,f⟩:=id S;obtain⟨k,-,-⟩:=e2d j g p n f
 have hN:∀ t∈Ar L 0 ⊓ iu L c,p4 (Bm+ t)=65:=λt q=> l t ((ei L 0 t).1 (U1.1 q).1).1
 obtain⟨e,d,h⟩:=glv hN o (λZ a=>((ei L 0 Z).1 (U1.1 a).1).2)
  (λZ a=>((ti L c Z).1 (U1.1 a).2).2)
 exact⟨k,⟨by rw[e];exact i,λm b=>(d m b).1,h,λm b=>(d m b).2⟩,e⟩
def ahD (L:Sq) (c:Fq): Prop :=
∀ (ob iy:Ft) (Yr Yc:Mt) (OU:Yr∈L ⊔ span ℂ {Bm}) (abe:Yr∉ L) (Xn:Yr (0,c)=0)
 (aif:Yr (0,bn c (rR ob))=0) (Kw:Yc∈L ⊔ span ℂ {Bm}) (abd:Yc∉ L) (Xm:Yc (0,c)=0)
 (aie:Yc (rR iy,c)=0) (w v:cq) (hw:w≠0) (hv:v≠0)
 (hR:bj w (gy ob (Yr (0,bn c (rR (ah ob 0)))) (-Yr (0,bn c (rR (ah ob 1)))))∈(Ar L 0 ⊓ iu L c).map (dq c))
 (dm:bj (gy iy (Yc (rR (ah iy 0),c)) (-Yc (rR (ah iy 1),c))) v∈(Ar L 0 ⊓ iu L c).map (dq c))
 (hy:Yr (0,bn c (rR (ah ob 0)))≠0\/Yr (0,bn c (rR (ah ob 1)))≠0)
 (hu:Yc (rR (ah iy 0),c)≠0\/Yc (rR (ah iy 1),c)≠0)
 (hn:∀ t:ℂ,bj (gy iy (Yc (rR (ah iy 0),c)) (-Yc (rR (ah iy 1),c))) v≠
   t•bj w (gy ob (Yr (0,bn c (rR (ah ob 0)))) (-Yr (0,bn c (rR (ah ob 1)))))),False
def gR0 (L:Sq) (c:Fq) (d b:Ft) (Y a:Mt): Prop :=
 Y∈L ⊔ span ℂ {Bm}/\Y∉ L/\Y (0,c)=0/\(∀ j,j≠d->Y (0,bn c (rR j))=0)/\a∈L ⊔ span ℂ {Bm}/\
 a∉ L/\a (0,c)=0/\a (rR b,c)=0/\a (rR (ah b 0),c)≠0/\a (rR (ah b 1),c)≠0/\
 bj (gy b (a (rR (ah b 0),c)) (-a (rR (ah b 1),c))) (single d 1)∈(Ar L 0 ⊓ iu L c).map (dq c)
def gK (L:Sq) (c:Fq): Prop :=
 ahD L c/\ ∀ (d a:Ft) (Y b:Mt),gR0 L c d a Y b-> ∀
 (Hz:∀ Z∈L,Z (0,c)=0->Z (0,bn c (rR d))=0/\Z (rR (ah a 0),c)=0/\Z (rR (ah a 1),c)=0),False
def gPK {L:Sq} (hL:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (h:c.val<2)
 (hq:finrank ℂ (L.map (Kl c))=2) (H:gH c ((Ar L 0 ⊓ iu L c).map (dq c)))
 {b a:Mt} (l:b∈Ar L 0) (z:o8 c b≠0) (n:a∈iu L c) (k:I8 c a≠0)
 :ahD L c:=by
 intro B A D C o e r g m d p f w v x hv u s y hu hn;obtain⟨i,j,q⟩:=gcx hL h hq l z n k o e r m d p;rw[gyc f]at i q;rw[gyr g]at j q;exact gpk c h _ H B A _ _ _ _ w v _ _ ⟨⟨x,hv,y,hu,u,s,hn⟩,i,j,q⟩
def gP2 {L c} X (S:gS L c X)
 (J:finrank ℂ ↥(Ar L 0)=4) (K:gK L c) d a Y Y' (R:gR0 L c d a Y Y'):False:=by
 obtain⟨A,h6,b,h0,hq,hX,W⟩:=id S;obtain⟨o,l,m,C,Mp,v,u,x,n,B,z⟩:=R;have y:=K.1
 have dd:∀ k,ah d k≠d:=λk=> by fin_cases d,k<;>decide
 have i:=C _ (dd 0);obtain⟨T,w,Q,M⟩:=grs A J b o l m i;have ae:∀ r:Ft,∀ j,j≠d->bj (gy a (Y' (rR (ah a 0),c)) (-Y' (rR (ah a 1),c))) (single d 1) (r,j)=0:=
  λr j hj=> by simp[bj,Q4,hj]
 have q:∀ k:Fin 2,gy a (Y' (rR (ah a 0),c)) (-Y' (rR (ah a 1),c)) (ah a k)≠0:=λk=> by
  fin_cases k<;>simp[(LP a _ _).2.1,(LP a _ _).2.2,n,B]
 by_cases g:∃ t:ℂ,bj (gy a (Y' (rR (ah a 0),c)) (-Y' (rR (ah a 1),c))) (single d 1)=
   t•bj w (gy (ah d 0) (Y (0,bn c (rR (ah (ah d 0) 0)))) (-Y (0,bn c (rR (ah (ah d 0) 1)))))
 swap
 · push_neg at g
   exact y _ a Y Y' o l m i Mp v u x w _ Q (by simp) M z T (Or.inl n) g
 obtain⟨t,ht⟩:=g;by_cases Ha:∃ Z∈L,Z (0,c)=0/\Z (0,bn c (rR d))≠0
 · obtain⟨Z,f,Ur,P⟩:=Ha
   obtain⟨Yd,F,G,p,H⟩:=gso A _ hX W f Ur P
   obtain⟨U,wd,hwd,N⟩:=grs A J b F G p H
   refine y d a Yd Y' F G p H Mp v u x wd _ hwd (by simp) N z U (Or.inl n) λs e=> q 0 ?_
   have :=congrFun e (ah a 0,d);simpa[bj,(LP d _ _).1] using this
 push_neg at Ha;by_cases Hb:∃ Z∈L,Z (0,c)=0/\ ∃ k:Fin 2,Z (rR (ah a k),c)≠0
 · obtain⟨Z,f,Ur,k,Us⟩:=Hb
   obtain⟨Ly,-,-,-,-,Qs,O7⟩:=gLp S
   obtain⟨Yt,t1,t2,t3,t4⟩:=gso Ly (bn c (rR (ah a k))) Qs O7 (S8 f)
    (by rw[Ip c b,(oq c b).1,(oq c b).2.1];exact Ur)
    (by rw[Ip c b,(oq c b).2.2.2,(oq c b).1];exact Us)
   obtain⟨Yk,k1,k2,k3,k4,hyk,V,hvk,O⟩:=gpb S t1 t2 t3 t4
   refine y _ _ Y Yk o l m i k1 k2 k3 k4 w V Q hvk M O T hyk λs e=> ?_
   have D:=congrFun e (ah a k,d);have E:=congrFun ht (ah a k,d)
   simp only[bj,Q6,Q5,(LP (ah a k) _ _).1,V6]at D E
   have od:w (ah a k)*gy (ah d 0) (Y (0,bn c (rR (ah (ah d 0) 0)))) (-Y (0,bn c (rR (ah (ah d 0) 1)))) d≠0:=
    λKj=> q k (by simpa[Kj] using E)
   have hs:s=0:=by rcases Q3.1 D.symm with h | h;exact h;exact absurd h od
   exact gne V (gy0 _ _ _ (hyk.imp id X9.2)) hvk (by rw[e,hs,T9])
 push_neg at Hb
 exact K.2 d a Y Y' ⟨o,l,m,C,Mp,v,u,x,n,B,z⟩ λZ f Ur=>⟨Ha Z f Ur,Hb Z f Ur 0,Hb Z f Ur 1⟩
def gQs {u y:cq} {a b:ℂ} (m:B9) (ha:a≠0) (c:b≠0) (h:Qf (a•u) (b•y) m=0):Qf u y m=0:=by
 rw[gqs,gqt]at h;simpa[ha,c] using h
lemma gPq {τ} (Iq:Xa 0 τ) {a b:cq} {m}:Qf a b (K6 τ m)=Qf (a∘ τ) (b∘ τ) m:=by
 rcases Iq with⟨-,rfl | rfl | rfl⟩ | ⟨h,-⟩<;>
  first | exact absurd h (by decide) | (simp[Qf,K6,ah,R1];ring)
def ahg {c:Fq} (b:c.val<2) {M} (H:gH c M) (d:bj ![0,1,-1] (single 0 1)∈M)
 {z:cq} (h:z 0=0) (z1:z 1≠0) (q1:∀ m∈M,Qf (single 0 1) (single 0 1) m=0)
 (f:∀ m∈M,Qf ![0,1,1] (single 0 1) m=0) (g:∀ m∈M,Qf ![0,1,1] z m=0):False:=by
 have s:(![1,0,0]:cq)=single 0 1:=by ext i;fin_cases i<;>rfl
 have e:dq c (XD c)=(11:ℂ)•bj ![0,1,-1] (single 0 1):=by
  funext ⟨i,j⟩;rcases I7 c b with rfl | rfl<;>fin_cases i,j<;>simp[dq,XD,bj,rR,bn,T0]
 refine ahk c b M H (e ▸ M.smul_mem _ d) (-(z 2/z 1)) (λm a=> s ▸ q1 m a)
  (λm a=> s ▸ f m a) λm a=> ?_
 have :=g m a
 rw[show z=z 1• ![0,1,-(-(z 2/z 1))] by ext i;fin_cases i<;>simp[h]<;>field_simp,gqt]at this
 exact (Q3.1 this).resolve_left z1
set_option maxHeartbeats 0 in
def anJ {c:Fq} (hc:c.val<2) {M} (H:gH c M) {j:Ft} (t:c=0\/j=0) {k:ℂ}
 (w:k≠0) (r:bj (gy j k (-k)) (single j 1)∈M) {z:cq} (l:z j=0) (v:z (ah j 0)≠0)
 (x:z (ah j 1)≠0) (q1:∀ m∈M,Qf (single j 1) (single j 1) m=0)
 (e:∀ m∈M,Qf (gy j 1 1) (single j 1) m=0) (f:∀ m∈M,Qf (gy j 1 1) z m=0):False:=by
 have d:bj (gy j 1 (-1)) (single j 1)∈M:=by
  convert M.smul_mem k⁻¹ r using 1;funext p;simp[bj,gy];split_ifs<;>field_simp
 by_cases j0:j=0
 · subst j0
   have o:∀ a b:ℂ,gy 0 a b= ![a*0,a,b]:=λa b=> by ext i;fin_cases i<;>simp[gy,ah]
   simp only[o,T6]at d e f;exact ahg hc H d l v q1 e f
 obtain rfl :=t.resolve_right j0
 have g:Xa 0 (swap 0 j):=by fin_cases j<;>first | exact absurd rfl j0 | decide
 have T:=λ(a b:cq) (q:∀ m∈M,Qf a b m=0) (a' b':cq) (n:a'=a∘ swap 0 j)
   (eb:b'=b∘ swap 0 j) (m:B9) (hm:m∈M.map (K6 (swap 0 j)))=> show Qf a' b' m=0 by
  obtain⟨m,h,rfl⟩:=hm;rw[gPq g,n,eb];convert q m h using 2<;>funext i<;>simp
 obtain⟨s,u⟩:∃ s:ℂ,bj ![0,1,-1] (single 0 1)=s•K6 (swap 0 j) (bj (gy j 1 (-1)) (single j 1)):=by
  fin_cases j
  .exact absurd rfl j0
  .refine⟨1,?_⟩;funext ⟨a,b⟩;fin_cases a,b<;>simp[K6,bj,gy,ah,T0,Q4]
  .refine⟨-1,?_⟩;funext ⟨a,b⟩;fin_cases a,b<;>simp[K6,bj,gy,ah,T0,Q4]
 refine ahg (by decide) (gHP g H) (u ▸ T4 _ s (S8 d))
  (by simpa using l) ?_ (T _ _ q1 _ _ ?_ ?_) (T _ _ e _ _ ?_ ?_) (T _ _ f _ _ ?_ rfl)<;>
  fin_cases j<;>(try exact absurd rfl j0)<;>(try funext i)<;>(try fin_cases i)<;>
   simp_all[gy,ah,Q4,T0]
def akw {L:Sq} (hL:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (j:c.val<2)
 (hq:finrank ℂ (L.map (Kl c))=2) (hA:finrank ℂ ↥(Ar L 0)=4) (H:gH c ((Ar L 0 ⊓ iu L c).map (dq c)))
 {a:Mt} (x:a∈Ar L 0) (N:o8 c a≠0)
 {d i0} Y {Y'} (R:gR0 L c d i0 Y Y')
 (v:∀ Z∈L,Z (0,c)=0->Z (0,bn c (rR d))=0/\Z (rR (ah i0 0),c)=0/\Z (rR (ah i0 1),c)=0)
 {g:Mt} (MY:g∈iu L c) (U:g (0,bn c (rR (ah d 0)))≠0) (V:g (0,bn c (rR (ah d 1)))≠0)
 (hC:Bm (rR (ah i0 0),c)*Y' (rR (ah i0 1),c)=Bm (rR (ah i0 1),c)*Y' (rR (ah i0 0),c)):False:=by
 obtain⟨u,P,q,l,A,LJ,y,S,Ld,T,hK⟩:=R
 have M:d=i0/\(c=0\/d=0):=by
  have s:=H.2.1 _ hK;rcases I7 c j with rfl | rfl<;>fin_cases d,i0<;>simp[dotProduct,eh,bj,gy,ah,rR,bn,Bm,
   S6,S9,Q4,T0]at s hC Ld T ⊢ <;>grind
 obtain⟨h,o⟩:=M;subst i0;have Q:∀ V1 i:Mt,V1∈L ⊔ span ℂ {Bm}->V1 (0,c)=0->i∈L ⊔ span ℂ {Bm}->i (0,c)=0->
   ∀ m∈(Ar L 0 ⊓ iu L c).map (dq c),Qf (o8 c V1) (I8 c i) m=0:=λV1 i h1 W h2 X m f=> by
  obtain⟨n,hn,rfl⟩:=f;exact gq1 hL j hq x N V1 i h1 W h2 X hn
 obtain⟨w,z⟩:=(ei L 0 a).1 x;obtain⟨-,J,K⟩:=v a w (z c);obtain⟨B,C⟩:=(ti L c g).1 MY;have zd:=(v g B (C 0)).1
 have b:∀ k,ah d k≠d:=λk=> by fin_cases d,k<;>decide
 have G:Y' (rR (ah d 1),c)=Y' (rR (ah d 0),c):=by
  have s:=H.2.1 _ hK;rcases I7 c j with rfl | rfl<;>fin_cases d<;>simp[dotProduct,eh,bj,gy,ah,rR,bn,S6,
   S9,Q4,T0]at s o ⊢ <;>grind
 have D:o8 c a=a (rR d,c)•single d 1:=funext λr=> by
  rcases (Mm d r).2.2.2 with e | e | e<;>subst r<;>simp[o8,Q4,J,K,b]
 have E:I8 c Y=Y (0,bn c (rR d))•single d 1:=funext λr=> by
  rcases (Mm d r).2.2.2 with e | e | e<;>subst r<;>simp[I8,Q4,l _ (b 0),l _ (b 1),b]
 have F:o8 c Y'=Y' (rR (ah d 0),c)•gy d 1 1:=funext λr=> by
  rcases (Mm d r).2.2.2 with e | e | e<;>subst r<;>
   simp[o8,gy,S,G,(b 0).symm,(b 1).symm,(Mm d 0).2.2.1]
 have O:a (rR d,c)≠0:=λh=> N (by rw[D,h,T9])
 have p:Y (0,bn c (rR d))≠0:=by
  have hy:=(grs hL hA j u P q (l _ (b 0))).1;fin_cases d<;>simpa[ah,l] using hy
 have q1:=Q a Y (Y9 w) (z c) u q;have q2:=Q Y' Y A y u q;have q3:=Q Y' g A y (Y9 B) (C 0)
 exact anJ j H o Ld (by rwa[G]at hK) zd U V
  (λm f=> gQs m O p (by rw[<- D,<- E];exact q1 m f))
  (λm f=> gQs m Ld p (by rw[<- F,<- E];exact q2 m f))
  (λm f=> by have :=q3 m f;rw[F,gqs]at this;exact (Q3.1 this).resolve_left Ld)
def an5 {L c X} (S:gS L c X)
 (B:finrank ℂ ↥(Ar L 0)=4) (H:gH c ((Ar L 0 ⊓ iu L c).map (dq c))) {b:Mt} (KX:b∈Ar L 0) (w:o8 c b≠0)
 {d a} Y Y' (R:gR0 L c d a Y Y')
 (i:∀ Z∈L,Z (0,c)=0->Z (0,bn c (rR d))=0/\Z (rR (ah a 0),c)=0/\Z (rR (ah a 1),c)=0)
 {f:Mt} (p:f∈iu L c) (t:f (0,bn c (rR (ah d 0)))≠0) (u:f (0,bn c (rR (ah d 1)))≠0):False:=by
 obtain⟨D,M,G,K,hq,N,J⟩:=id S;obtain⟨E,x,y,z,q,m,l,Ny,o,s,C⟩:=R;by_cases v:Bm (rR (ah a 0),c)*Y' (rR (ah a 1),c)=Bm (rR (ah a 1),c)*Y' (rR (ah a 0),c)
 .exact akw D G hq B H KX w Y ⟨E,x,y,z,q,m,l,Ny,o,s,C⟩ i p t u v
 obtain⟨j,n⟩:=(ei L 0 b).1 KX;obtain⟨-,g,hZb⟩:=i b j (n c);exact gRI L c X S d a Y' q m l Ny o s v b j (n c)
  (λh=> w (funext λr=> by rcases (Mm a r).2.2.2 with e | e | e<;>subst r<;>simp[o8,h,g,hZb]))
  (λk=> by fin_cases k;exacts [g,hZb])
  (λZ F A=>(i Z F A).1) f p t u
def gKE L c X (S:gS L c X)
 (C:finrank ℂ ↥(Ar L 0 ⊓ iu L c)=3):gK L c:=by
 obtain⟨E,W,o,V,hq,Z,O⟩:=id S;obtain⟨n,H,-⟩:=gNH S C.ge;obtain⟨⟨Z0,KX,K⟩,⟨a,f,KR⟩⟩:=gZ o n (e2d W V hq Z O).2.1 C;have y:=gPK E o hq H KX K f KR
 refine⟨y,λd M Y A R p=> ?_⟩
 obtain⟨G,q,t,Py,w,v,u,x,i,Q,D⟩:=R
 have U:∀ k,ah d k≠d:=λk=> by fin_cases d,k<;>decide
 have l:=((ti L c a).1 f).1;have B:=((ti L c a).1 f).2;have N:=(p a l (B 0)).1;by_cases Hc:a (0,bn c (rR (ah d 0)))=0\/a (0,bn c (rR (ah d 1)))=0
 · obtain⟨k,hk⟩:∃ k:Fin 2,a (0,bn c (rR (ah d k)))=0:=Hc.elim (⟨0,·⟩) (⟨1,·⟩)
   have F:Y+ a∈L ⊔ span ℂ {Bm}:=V7 _ G (Y9 l)
   have hVL:Y+ a∉ L:=λh=> q (by simpa using L.sub_mem h l)
   have z:(Y+ a) (0,c)=0:=by simp[t,B 0]
   have hVo:(Y+ a) (0,bn c (rR (ah d k)))=0:=by simp[Py _ (U k),hk]
   obtain⟨T,w2,hw2,P⟩:=grs E n o F hVL z hVo
   refine y _ M _ A F hVL z hVo w v u x w2 _ hw2 (by simp) P D T (Or.inl i) λs e=> KR ?_
   rcases Y8 s 0 with rfl | hs
   .exact absurd (by simpa using e) (gne _ (gy0 M _ _ (Or.inl i)) (by simp))
   obtain⟨r,J⟩:=Ap.1 hw2;rw[W0]at J
   have g:=gyr hVo
   funext j;by_cases hjd:j=d
   .subst hjd;simpa[I8] using N
   · have b:=congrFun e (r,j);simp[bj,Q4,hjd,hs,J]at b
     have m:=congrFun g j;simp only[I8,Ac,Ad,R5]at m
     rw[Py j hjd,Y0]at m
     simp only[I8,Ac,Ad,W0,m]
     simp only[gy]at b ⊢;split_ifs at b ⊢ <;>first | exact b | exact Bk.1 b | rfl | linear_combination -b
 push_neg at Hc;exact an5 S n H KX K Y A ⟨G,q,t,Py,w,v,u,x,i,Q,D⟩
  p f Hc.1 Hc.2
def Sh (o:Ft) (w:cq):B9:=λp=> if p.2=o then oj w p.1 else 0
set_option maxHeartbeats 0 in
def anP (c:Fq) (f:c.val<2) oR (w z:cq) (m:B9) (e a:ℂ)
 (h:(lj c).mulVec m=e•eh c+ a•Sh oR w) (i:dotProduct (eh c) m=0) (j:dotProduct (Sh oR w) m=0)
 (q:Qf w z m=0) (o:dotProduct (eh c) (bj w z)=0) (n: ∑ r,SM c r oR* ∑ k,j1 w r k*w k=0)
 (u:z oR=0) (s:z (ah oR 0)≠0) (t:z (ah oR 1)≠0)
 (g:Nv w):a=0:=by
 have l:=λp=> congrFun h p
 clear h;rcases I7 c f with rfl | rfl<;>simp +decide [LN,lj,eh,mulVec,dotProduct,S6,S9,Bm,rR,bn,Prod.forall,U3]at * <;>fin_cases oR<;>
  simp +decide [Sh,eh,SM,bj,oj,j1,Qf,ah,S9,Bm,rR,bn,Prod.forall,U3]at * <;>
  rcases g with⟨b,d⟩ | ⟨b,d⟩ | ⟨b,d⟩<;>grind (splits :=20)
lemma ahq {c:Fq} (hc:c.val<2) {m:B9} {a:ℂ} (h:(lj c).mulVec m=a•eh c)
 (b:dotProduct (eh c) m=0):a=0:=by
 have d:=λp=> congrFun h p
 clear h;rcases I7 c hc with rfl | rfl<;>
  simp +decide [LN,lj,eh,mulVec,dotProduct,S6,S9,Bm,rR,bn,
   Prod.forall,U3]at * <;>grind
def gL1 (c:Fq) (g:c.val<2) (M:Submodule ℂ B9) (C:4≤ finrank ℂ M)
 (f:∀ m∈M,dotProduct (eh c) m=0) (l:∀ m∈M,∀ m'∈M,dotProduct m ((lj c).mulVec m')=0)
 (q:∀ m∈M,p3 m=0) (o:Ft) w z (hR:bj w z∈M) (d:z o=0) (za:z (ah o 0)≠0)
 (j:z (ah o 1)≠0) (r:Nv w):False:=by
 have la:∀ m∈M,dotProduct (Sh o w) m=0:=λm hm=> by
  have P:=gP3 q w z hR m hm
  have e:∀ i,∑ k,m (i,k)*oj z k=z (ah o 0)*z (ah o 1)*m (i,o):=λi=>
   (Bp rfl λk _=> Az _ _).trans (Xd (λk=> m (i,k)) d)
  simp only[e]at P
  have y:z (ah o 0)*z (ah o 1)* ∑ i,oj w i*m (i,o)=0:=by
   rw[Ao,<- P];exact Bp rfl λi _=> by ring
  have k:=(Q3.1 y).resolve_left (mul_ne_zero za j);simpa[dotProduct,Sh,S6] using k
 have sw:∃ i,oj w i≠0:=by
  rcases r with⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
  exacts [⟨2,by simp[oj,a,b]⟩,⟨1,by simp[oj,a,b]⟩,⟨0,by simp[oj,a,b]⟩]
 have hv:LinearIndependent ℂ ![eh c,Sh o w]:=by
  rw[Cl];intro s t e
  have x:s=0:=by
   have :=congrFun e (o,ah o 0);simp only[R5,Q6,Q5,Sh,if_neg (Mm o 0).1,T6,S0,W0]at this
   exact (Q3.1 this).resolve_right (by simp only[eh];split_ifs<;>norm_num)
  subst x;obtain⟨i,v⟩:=sw;have :=congrFun e (i,o);simp[Sh,v]at this;exact⟨rfl,this⟩
 obtain⟨m,hm,B,p⟩:=YM M (lj c) (Vf g) ![eh c,Sh o w] hv (show 9< finrank ℂ M+ finrank ℂ M+2 by omega)
  (λn hn i=> by fin_cases i<;>simp[f n hn,la n hn]) l
 obtain⟨a,ha⟩:=(An ℂ).1 p;simp only[Ag,Dd,De,Matrix.head_cons]at ha;have A:=l _ hR _ hR;rw[ahn c w w d d]at A;have u:=anP c g o w z m (a 0) (a 1) ha.symm (f m hm) (la m hm)
  (Ue q (by rw[show z 0*z 1*z 2=0 by fin_cases o<;>simp at d<;>simp[d],T6]) hR m hm) (f _ hR)
  ((Q3.1 A).resolve_left (by intro h;apply mul_ne_zero za j;linear_combination h/2)) d za j r
 rw[u,T9,S0]at ha;have a0:=ahq g ha.symm (f m hm);rw[a0,T9]at ha
 exact B (Vf g (by rw[<- ha,Bv]))
def ahs {w g:cq} (hw:w≠0) (c:∀ k,g k≠0) (d: ∑ k,g k*w k=0) (i:Ft):
 ∃ r,j1 w r i≠0:=by
 by_contra h;push Not at h;apply hw;have a:=h 0;have b:=h 1;have e:=h 2;fin_cases i<;>simp[j1]at a b e<;>funext k<;>fin_cases k<;>simp_all[R1]
def ahi {w:cq} (d:w≠0):∃ t:ℂ,t≠0/\YO (t•w):=by
 unfold YO;simp only[Q6,Q5];by_cases a:w 0=0
 · by_cases b:w 1=0
   · have c:w 2≠0:=λc=> d (funext λk=> by fin_cases k<;>assumption)
     exact⟨(w 2)⁻¹,Cr c,Or.inr (Or.inr ⟨by simp[a],by simp[b],V9 c⟩)⟩
   .exact⟨(w 1)⁻¹,Cr b,Or.inr (Or.inl ⟨by simp[a],V9 b⟩)⟩
 .exact⟨(w 0)⁻¹,Cr a,Or.inl (V9 a)⟩
def anu (c:Fq) (g:c.val<2) (M:Submodule ℂ B9) (K:4≤ finrank ℂ M)
 (b:∀ m∈M,dotProduct (eh c) m=0) (B:∀ m∈M,∀ G∈M,dotProduct m ((lj c).mulVec G)=0)
 (hp:∀ m∈M,p3 m=0) (d i:Ft) (w v:cq) (hR:bj w (single d 1)∈M) (h:w≠0)
 (dm:bj (single i 1) v∈M) (hv:v≠0):False:=by
 obtain⟨t,J,p⟩:=ahi h;obtain⟨z,A,o⟩:=ahi hv;obtain⟨w,hR,h,p⟩:∃ w:cq,bj w (single d 1)∈M/\w≠0/\YO w:=
  ⟨t•w,by rw[(Na).2];exact M.smul_mem t hR,Y5 J h,p⟩
 obtain⟨v,dm,hv,o⟩:∃ v:cq,bj (single i 1) v∈M/\v≠0/\YO v:=
  ⟨z•v,by rw[(Na).1,(Na).2];exact M.smul_mem z dm,Y5 A hv,o⟩
 have Q1:=Ue hp (by fin_cases d<;>simp) hR
 have f:=Ue hp (by fin_cases i<;>simp) dm
 have x:∀ m∈M,dotProduct (bj (λr=> j1 w r i) (λj=> j1 v j d)) m=0:=λm hm=> by
  have k:dotProduct (bj (λr=> j1 w r i) (λj=> j1 v j d)) m= ∑ r,(∑ k,j1 w r k*(single i 1:cq) k)*
    ∑ j,m (r,j)* ∑ l,j1 (single d 1) j l*v l:=by
   fin_cases i,d<;>simp[dotProduct,bj,S6,R1,j1]<;>ring
  rw[k,<- Vg,f _ (M.add_mem hR hm),f _ hR,f m hm,X4,X4]
 have q:∀ k,eh c k≠0:=λk=> by simp only[eh];split_ifs<;>norm_num
 obtain⟨r,E⟩:=ahs h (λk=> q (k,d)) (by
  simpa[dotProduct,bj,S6,Q4] using b _ hR) i
 obtain⟨j,C⟩:=ahs hv (λk=> q (i,k)) (by
  simpa[dotProduct,bj,S6,Q4,Az] using b _ dm) d
 have D:LinearIndependent ℂ ![eh c,bj (λr=> j1 w r i) (λj=> j1 v j d)]:=by
  rw[Cl];intro s t e
  have F:s=0:=by
   have :=congrFun e (i,d);simp only[R5,Q6,Q5,bj,W0]at this
   rw[show j1 w i i=0 by fin_cases i<;>rfl,V6,T6,S0]at this
   exact (Q3.1 this).resolve_right (q _)
  subst F;have :=congrFun e (r,j);simp[bj,E,C]at this;exact⟨rfl,this⟩
 obtain⟨m,hm,H,hGm⟩:=YM M (lj c) (Vf g) _ D (show 9< finrank ℂ M+ finrank ℂ M+2 by omega)
  (λn hn i=> by fin_cases i<;>simp[b n hn,x n hn]) B
 obtain⟨a,ha⟩:=(An ℂ).1 hGm;simp only[Ag,Dd,De]at ha;by_cases b0:a 1=0
 · rw[b0,T9,S0]at ha
   rw[ahq g ha.symm (b m hm),T9]at ha
   exact H (Vf g (by rw[<- ha,Bv]))
 have sm:∀ u y:cq,Qf u y ((a 1)⁻¹•m)=(a 1)⁻¹^2*Qf u y m:=λu y=> by
  simp only[Qf,Q6,Q5,R1];ring
 refine anQ c g d i w v ((a 1)⁻¹•m) ((a 1)⁻¹*a 0) ?_ (by rw[Co,b m hm,Z6])
  (by rw[Co,x m hm,Z6]) (by rw[sm,Q1 m hm,T6]) (by rw[sm,f m hm,T6])
  (b _ hR) (b _ dm) p o
 rw[Matrix.mulVec_smul,<- ha,smul_add,Ae,Ae,V9 b0,Aw]
def gcl (j:Ft):B9→ₗ[ℂ] (cq) where
 toFun n r:=n (r,j)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def Ui {k:ℕ} (A:Fin k->cq) (j:Ft):B9→ₗ[ℂ] (Fin k->ℂ) where
 toFun n r:= ∑ s,A r s*n (s,j)
 map_add' a b:=by funext r;simp[mul_add,Finset.sum_add_distrib]
 map_smul' a b:=by funext r;simp[Ao,mul_left_comm]
def gqk {L:Sq} (o:∀ t∈L,p4 (Bm+ t)=65) {c:Fq} (q:c.val<2) {V:Mt}
 (p:V∈L ⊔ span ℂ {Bm}) (Uo:V (0,c)=0) (hVL:V∉ L) {n:Mt} (hn:n∈Ar L 0 ⊓ iu L c):
 Qf (o8 c V) (I8 c V) (dq c V+ dq c n)=Qf (o8 c V) (I8 c V) (dq c V)/\
  Qf (o8 c V) (I8 c V) (dq c V)≠0:=by
 obtain⟨X,f,m,hm,a⟩:=V0.1 p;obtain⟨l,rfl⟩:=X3.1 hm;obtain⟨k,h2⟩:=U1.1 hn;obtain⟨g,hr⟩:=(ei L 0 n).1 k;obtain⟨-,r⟩:=(ti L c n).1 h2
 have b:∀ s:ℂ,Qf (o8 c V) (I8 c V) (dq c V+ s•dq c n)=65*l^4:=λs=> by
  have e:=gbx q (V+ s•n) (by simp[Uo,hr])
  rw[show V+ s•n=l•Bm+(X+ s•n) by rw[<- a];abel,Ud L o _ (L.add_mem f (L.smul_mem s g)) l,
   show l•Bm+(X+ s•n)=V+ s•n by rw[<- a];abel]at e
  rw[S4,S4,S4,S5,S5,S5,show o8 c n=0 from funext λi=> r _,
   show I8 c n=0 from funext λj=> hr _,Z6,S0,S0]at e
  exact e.symm
 have k1:=b 1;have d:=b 0;rw[Aw]at k1;rw[T9,S0]at d
 have u:l≠0:=λh=> hVL (by rw[<- a,h,T9,S0];exact f)
 exact⟨by rw[k1,d],by rw[d];exact mul_ne_zero (by norm_num) (pow_ne_zero _ u)⟩
def gIB {k:ℕ} (f g:B9→ₗ[ℂ] (Fin k->ℂ)) (M:Submodule ℂ B9) (x:B9)
 (h:∀ n∈M,f (x+ n) ⬝ᵥ g (x+ n)=f x ⬝ᵥ g x) (q:f x ⬝ᵥ g x≠0):
 ∃ K:Submodule ℂ B9,(∀ n∈K,n∈M/\f n=0/\g n=0)/\finrank ℂ M+1≤ k+ finrank ℂ K:=by
 set Φ:B9→ₗ[ℂ] (Fin 2× Fin k->ℂ):=LinearMap.pi λp:Fin 2× Fin k=>
  if p.1=0 then (LinearMap.proj p.2).comp f else (LinearMap.proj p.2).comp g
 set S:=LinearMap.funLeft ℂ ℂ (λp:Fin 2× Fin k=>(1- p.1,p.2))
 have d:∀ n∈M,f x ⬝ᵥ g n+ f n ⬝ᵥ g x=0/\f n ⬝ᵥ g n=0:=λn hn=> by
  have e1:=h n hn;have e2:=h (-n) (M.neg_mem hn);simp only[S4,map_neg,Ct,Bu,neg_dotProduct,dotProduct_neg]at e1 e2
  exact⟨by linear_combination (e1- e2)/2,by linear_combination (e1+ e2)/2⟩
 have c:∀ a b,Φ a ⬝ᵥ S (Φ b)=
   f a ⬝ᵥ g b+ f b ⬝ᵥ g a:=λa b=> by
  simp[Φ,S,dotProduct,S6,Ag,LinearMap.funLeft_apply,Az]
 set P:=M.map Φ
 have hx:Φ x∉ P:=by
  rintro⟨n,hn,e⟩;apply q;have l:=c n n;rw[e,c]at l;linear_combination l/2+(d n hn).2
 have inj:Function.Injective S:=
  LinearMap.funLeft_injective_of_surjective _ _ _ λp=>⟨(1- p.1,p.2),by simp⟩
 have o:=Sw (P ⊔ span ℂ {Φ x}) (P.map S)
  (λa r b s=> by
   obtain⟨y,j,z,u,rfl⟩:=V0.1 r;obtain⟨t,rfl⟩:=X3.1 u;obtain⟨_,⟨m,Ni,rfl⟩,rfl⟩:=Af.1 s;obtain⟨n,hn,rfl⟩:=j;rw[Ct,smul_dotProduct,c,c,(d m Ni).1];have :=(d _ (M.add_mem hn Ni)).2;simp only[S4,Ct,Bu]at this;rw[Z6,S0];linear_combination this -(d n hn).2-(d m Ni).2)
 rw[<- Y3 (equivMapOfInjective _ inj P)]at o;have lt:finrank ℂ ↥P< finrank ℂ ↥(P ⊔ span ℂ {Φ x}):=Dc
  (Z9 Ce λe=> hx (by rw[e];exact Submodule.mem_sup_right (Ay _)))
 have rn:=Ch (Φ.domRestrict M)
 rw[LinearMap.range_domRestrict,Y3 (equivMapOfInjective M.subtype (λa b h=> Subtype.ext h) _)]at rn
 change finrank ℂ ↥P+ _=_ at rn;rw[Fintype.card_prod,Bc,Bc]at o
 refine⟨(ker (Φ.domRestrict M)).map M.subtype,λn hn=> ?_,by omega⟩
 obtain⟨y,j,rfl⟩:=hn
 have e:=λp=> congrFun (Am.1 j) p
 exact⟨y.2,funext λi=> by simpa[Φ] using e (0,i),funext λi=> by simpa[Φ] using e (1,i)⟩
lemma gqA {d:Ft} {v:cq} {n:B9}:Qf v (single d 1) n=
  gcl (ah d 0) n ⬝ᵥ Ui (j1 v) (ah d 1) n:=by
 fin_cases d<;>simp[Qf,gcl,Ui,j1,ah,dotProduct,mulVec,R1,Q4]<;>ring
def gfA (a:Ft) (v:cq):Fin 2->cq:= ![single a 1,j1 v a]
def gfB (a:Ft) (v:cq):Fin 2->cq:= ![j1 v a,single a 1]
lemma gqB {i0} {d:Ft} {p q} {n:B9}:Qf (gy i0 p q) (single d 1) n=
  Ui (gfA i0 (gy i0 p q)) (ah d 0) n ⬝ᵥ Ui (gfB i0 (gy i0 p q)) (ah d 1) n:=by
 fin_cases d,i0<;>simp[Qf,gcl,Ui,j1,ah,gy,gfA,gfB,dotProduct,mulVec,R1,
  Ag,Q4]<;>ring
def an6 {d:Ft} {v:cq} (hv:∀ k,v k≠0) {n:B9} (ha:gcl (ah d 0) n=0)
 (c:Ui (j1 v) (ah d 1) n=0):
 n=bj (λr=> n (r,d)) (single d 1):=by
 have a:=λr=> congrFun ha r;have b:=λr=> congrFun c r
 have :=hv 0;have :=hv 1;have :=hv 2;funext ⟨r,j⟩;fin_cases d,j<;>
  simp[gcl,Ui,j1,bj,dotProduct,R1,Q4,ah,U3]at a b ⊢ <;>
  fin_cases r<;>grind
def YU (c:Fq) (d a:Ft) (p q:ℂ):Fin 5->B9:=
 ![eh c,bj (single a 1) (single (ah d 0) 1),bj (j1 (gy a p q) a) (single (ah d 0) 1),
  bj (j1 (gy a p q) a) (single (ah d 1) 1),bj (single a 1) (single (ah d 1) 1)]
def an3 {c:Fq} (b:c.val<2) d i0 {p q:ℂ} (f:p≠0) (hq:q≠0):
 LinearIndependent ℂ (YU c d i0 p q):=by
 rw[Ax];intro g e
 have a:=λx=> congrFun e x
 rcases I7 c b with rfl | rfl<;>fin_cases d,i0<;>
  simp +decide [YU,eh,bj,j1,gy,ah,S9,rR,bn,Prod.forall,U3,Q4]
   at a ⊢ <;>grind
set_option maxHeartbeats 0 in
def gk5 {c:Fq} (f:c.val<2) {d i0 p q} {m:B9} {a:Fin 5->ℂ}
 (h:(lj c).mulVec m= ∑ k,a k•YU c d i0 p q k) (b:∀ k,dotProduct (YU c d i0 p q k) m=0) (g:p≠0)
 (e:eh c (ah i0 0,d)*p=eh c (ah i0 1,d)*q):m=0:=by
 have h1:=λx=> congrFun h x
 clear h;rcases I7 c f with rfl | rfl<;>simp +decide [LN,lj,mulVec,dotProduct,S6,S9,Bm,rR,bn,Prod.forall,U3]at h1 b<;>fin_cases d,i0<;>
  simp +decide [YU,eh,bj,j1,gy,ah,rR,bn,Q4,Bd,Prod.forall,U3]at h1 b e ⊢ <;>grind
def an4 L c X (S:gS L c X)
 (h4:4≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c)) d i0 Y Y' (R:gR0 L c d i0 Y Y')
 (V:∀ Z∈L,Z (0,c)=0->Z (0,bn c (rR d))=0/\Z (rR (ah i0 0),c)=0/\Z (rR (ah i0 1),c)=0):False:=by
 obtain⟨hL,h6,b,h0,hq,hX,K9⟩:=id S;obtain⟨J,s,Kw,Py,Mp,LJ,LA,Ny,Ld,OX,hK⟩:=R
 obtain⟨-,H,hf⟩:=gNH S (by omega)
 have hM:4≤ finrank ℂ ↥((Ar L 0 ⊓ iu L c).map (dq c)):=by rw[hf];exact h4
 obtain⟨X1,u,m1,N,C⟩:=V0.1 J;obtain⟨l,rfl⟩:=X3.1 N;obtain⟨X2,v,m2,Me,D⟩:=V0.1 Mp;obtain⟨g,rfl⟩:=X3.1 Me
 have P:l≠0:=by rintro rfl;apply s;rw[<- C,T9,S0];exact u
 have Q:g≠0:=by rintro rfl;apply LJ;rw[<- D,T9,S0];exact v
 have E:∀ p,(g•X1- l•X2) p=g*Y p- l*Y' p:=λp=> by rw[<- C,<- D];simp;ring
 have Z:=V _ (L.sub_mem (L.smul_mem g u) (L.smul_mem l v)) (by rw[E,Kw,LA];ring)
 simp only[E]at Z
 have y0:I8 c Y=Y (0,bn c (rR d))•single d 1:=funext λj=> by
  by_cases o:j=d
  .subst o;simp[I8]
  .simp[I8,o,Py j o]
 have DS:∀ n∈(Ar L 0 ⊓ iu L c).map (dq c),Qf (o8 c Y) (single d 1) (dq c Y+ n)=
   Qf (o8 c Y) (single d 1) (dq c Y)/\Qf (o8 c Y) (single d 1) (dq c Y)≠0:=by
  rintro _ ⟨n,hn,rfl⟩;have k:=gqk hL b J Kw s hn;rw[y0,gqt,gqt]at k;exact⟨mul_left_cancel₀ (left_ne_zero_of_mul k.2) k.1,right_ne_zero_of_mul k.2⟩
 have D0:=(DS 0 (Submodule.zero_mem _)).2
 have r:Y (rR (ah i0 0),c)≠0:=λe=> mul_ne_zero P Ld (by linear_combination -Z.2.1+ g*e)
 have T:Y (rR (ah i0 1),c)≠0:=λe=> mul_ne_zero P OX (by linear_combination -Z.2.2+ g*e)
 set p:=Y (rR (ah i0 0),c);set q:=Y (rR (ah i0 1),c);set M:=(Ar L 0 ⊓ iu L c).map (dq c);by_cases U:Y (rR i0,c)=0
 · have hv:o8 c Y=gy i0 p q:=funext λk=> by
    rcases (Mm i0 k).2.2.2 with rfl | rfl | rfl
    .rw[(LP _ _ _).1];exact U
    .rw[(LP _ _ _).2.1];rfl
    .rw[(LP _ _ _).2.2];rfl
   rw[hv]at DS D0
   obtain⟨K,hK5,hd⟩:=gIB (Ui (gfA i0 (gy i0 p q)) (ah d 0))
    (Ui (gfB i0 (gy i0 p q)) (ah d 1)) M (dq c Y)
    (λn hn=> by simp only[<- gqB];exact (DS n hn).1) (by simp only[<- gqB];exact D0)
   have B:∀ n∈K,∀ k,dotProduct (YU c d i0 p q k) n=0:=λn hn k=> by
    obtain⟨h1,h2,G⟩:=hK5 n hn;have w:=congrFun h2 0;have a1:=congrFun h2 1;have z:=congrFun G 0;have A:=congrFun G 1;simp[Ui,gfA,gfB]at w a1 z A;fin_cases k<;>simp[YU,Rj]<;>first | exact H.2.1 n h1 | exact w | exact a1 | exact z | exact A
   obtain⟨m,hm,m0,hGm⟩:=YM K (lj c) (Vf b) _ (an3 b d i0 r T) (show 9< finrank ℂ K+ finrank ℂ K+5 by omega) B
    λn hn n' Ni=> H.2.2.1 n (hK5 n hn).1 n' (hK5 n' Ni).1
   obtain⟨a,ha⟩:=(An ℂ).1 hGm
   refine m0 (gk5 b ha.symm (B m hm) r ?_)
   have F:=H.2.1 _ hK;rw[Ah,Rj,aeJ i0,(LP _ _ _).1,(LP _ _ _).2.1,(LP _ _ _).2.2]at F
   exact mul_left_cancel₀ Q (by linear_combination eh c (ah i0 0,d)*Z.2.1- eh c (ah i0 1,d)*Z.2.2+ l*F)
 · have vz:∀ k,o8 c Y k≠0:=λk=> by rcases (Mm i0 k).2.2.2 with rfl | rfl | rfl;exacts [U,r,T]
   obtain⟨K,f,hd⟩:=gIB (gcl (ah d 0)) (Ui (j1 (o8 c Y)) (ah d 1)) M (dq c Y) (λn hn=> by simp only[<- gqA];exact (DS n hn).1)
    (by simp only[<- gqA];exact D0)
   have i:=λy (O:y∈K)=> an6 vz (f y O).2.1 (f y O).2.2
   have W:K≠ ⊥ :=λh=> by rw[h,V3]at hd;omega
   obtain⟨n,hn,n0⟩:=Bt W
   obtain⟨n',Ni,hi⟩:∃ n'∈K,∀ t:ℂ,n'≠t•n:=by
    by_contra b;push Not at b
    have :=W1 (show K≤ ℂ ∙ n from λx hx=> by
     obtain⟨t,rfl⟩:=b x hx;exact T4 _ t (Ay n))
    rw[Ab n0]at this;omega
   refine ahp b H d (by rw[<- i n hn];exact (f n hn).1)
    (by rw[<- i n' Ni];exact (f n' Ni).1) (λt e=> hi t ?_) λe=> n0 ?_
   .rw[i n' Ni,e,(Na).2,<- i n hn]
   .rw[i n hn,e];funext p;simp[bj]
def gPN {c:Fq} (hc:c.val<2) {M} (H:gH c M) (h4:4≤ finrank ℂ M) ob iy
 {y0 y1 u0 u1} w v (D:gD0 M ob iy y0 y1 u0 u1 w v):False:=by
 have ⟨hw,hv,u,hu,f,dm,_⟩:=D;obtain⟨n,o,q⟩:=LP ob y0 (-y1);obtain⟨l,k,j⟩:=LP iy u0 (-u1);by_cases a:y0≠0/\y1≠0/\(Nv w)
 .exact gL1 c hc M h4 H.2.1 H.2.2.1 H.2.2.2 ob w _ f n (by rw[o];exact a.1) (by rw[q];exact X9.2 a.2.1) a.2.2
 by_cases b:u0≠0/\u1≠0/\(Nv v)
 · have T:=gHT hc H
   have inj:Function.Injective Qp:=λa b h=> funext λp=> by simpa[Qp] using congrFun h (p.2,p.1)
   exact gL1 c hc _ (by rw[<- Y3 (equivMapOfInjective _ inj M)];exact h4) T.2.1 T.2.2.1
    T.2.2.2 iy v _ (by rw[<- XK];exact S8 dm) l (by rw[k];exact b.1)
    (by rw[j];exact X9.2 b.2.1) b.2.2
 refine gpl c hc M H ob iy y0 y1 u0 u1 w v D (λt x=> ?_) ?_ ?_
 · obtain⟨d,a,-,r,-,e,-⟩:=UT ob t u;obtain⟨i,y,-,g,-,m,-⟩:=UT iy x hu
   rw[e,(Na).1]at f;rw[m,<- (Na).1]at dm
   exact anu c hc M h4 H.2.1 H.2.2.1 H.2.2.2 d i _ _ f (Y5 r hw) dm (Y5 g hv)
 · by_cases s:y0=0\/y1=0;exact Or.inl s
   push_neg at s;exact Or.inr ((gtp hw).resolve_right λh2=> a ⟨s.1,s.2,h2⟩)
 · by_cases s:u0=0\/u1=0;exact Or.inl s
   push_neg at s;exact Or.inr ((gtp hv).resolve_right λh2=> b ⟨s.1,s.2,h2⟩)
def gKN L c X (S:gS L c X)
 (a:4≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c)):gK L c:=by
 obtain⟨o,n,e,m,q,p,l⟩:=id S
 obtain⟨-,H,f⟩:=gNH S (by omega)
 exact⟨λk j _ _ _ _ _ _ _ _ _ _ w v h hv d b i g hn=>
  gPN e H (by rw[f];exact a) k j w v ⟨h,hv,i,g,d,b,hn⟩,an4 L c X S a⟩
lemma gF2 c {o o':Ft} {a b:cq} (d:a o'=0) (e:b o=0):
 dotProduct (bj a b) ((lj c).mulVec (bj a b))=4*SM c o' o*(a (ah o' 0)*a (ah o' 1))*(b (ah o 0)*b (ah o 1)):=by
 rw[aa5 c b b d d];fin_cases o<;>simp[j1,ah,R1]at e ⊢ <;>rw[e]<;>ring
def gF1 {c:Fq} (a:c.val<2) {i d:Ft} {s:ℂ}
 (h:dotProduct (eh c) (s•bj (single i 1) (single d 1))=0):s=0:=by
 rcases I7 c a with rfl | rfl<;>fin_cases i,d<;>
  simpa[dotProduct,S6,R1,bj,eh,rR,bn,T0] using h
def gtI {c:Fq} (hc:c.val<2):Function.Injective (ig c):=λa b h=> by
 funext ⟨i,j⟩;have :=congrFun h (bn c j,bn c i);simpa[Ip c hc,(oq c hc).2.2.2] using this
def gFL {L c X} (S:gS L c X)
 (h3:3≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c)) (K:gK L c) (K':gK (L.map (ig c)) c):False:=by
 obtain⟨hL,h6,hc,h0,hq,hX,K9⟩:=id S;obtain⟨hA,H,-⟩:=gNH S h3;obtain⟨o,am,Y,y,I2,Kw,u⟩:=aeI hL h0 hX K9;obtain⟨ob,rfl⟩:=gob hc am;obtain⟨Q,w,A,m⟩:=grs hL hA hc y I2 Kw u;obtain⟨U,T,-,f,W,J,O7⟩:=gLp S;obtain⟨o',ae,Yt,t1,t2,t3,t4⟩:=aeI U f J O7;obtain⟨iy,rfl⟩:=gob hc ae;obtain⟨Y',G,F,E,p,z,v,hv,dm⟩:=gpb S t1 t2 t3 t4;by_cases O:∃ t:ℂ,bj (gy iy (Y' (rR (ah iy 0),c)) (-Y' (rR (ah iy 1),c))) v=
   t•bj w (gy ob (Y (0,bn c (rR (ah ob 0)))) (-Y (0,bn c (rR (ah ob 1)))))
 swap
 · push_neg at O
   exact K.1 ob iy Y Y' y I2 Kw u G F E p w v A hv m dm Q z O
 obtain⟨t,ht⟩:=O
 have XZ:t≠0:=by
  rintro rfl;exact gne _ (gy0 _ _ _ (z.imp id X9.2)) hv (by simpa using ht)
 set R:=Y (0,bn c (rR (ah ob 0)));set y1:=Y (0,bn c (rR (ah ob 1)));set B:=Y' (rR (ah iy 0),c);set C:=Y' (rR (ah iy 1),c);obtain⟨g0,x,g2⟩:=LP ob R (-y1);obtain⟨VY,Uh,UR⟩:=LP iy B (-C)
 have P:=λr s=> congrFun ht (r,s);simp only[bj,Q6,Q5]at P
 by_cases h:R=0\/y1=0<;>by_cases WK:B=0\/C=0
 ·
  obtain⟨d,a,-,N,-,e,-⟩:=UT ob h Q;obtain⟨i,a',-,al,-,q,-⟩:=UT iy WK z;rw[e]at m P;rw[q]at P
  have k:∀ r,r≠i->w r=0:=λr g=> by
   have :=P r d;simp[Q4,g,XZ,N]at this;exact this
  have D:w i≠0:=λf=> A (funext λr=> by rcases Y8 r i with rfl | g;exacts [f,k r g])
  have ag:bj w (a•single d 1)=(a*w i)•bj (single i 1) (single d 1):=by
   funext ⟨r,s⟩;by_cases g:r=i
   .subst g;simp[bj];ring
   .simp[bj,k r g,Q4,g]
  rw[ag]at m;exact mul_ne_zero N D (gF1 hc (H.2.1 _ m))
 ·
  push_neg at WK;obtain⟨d,a,b,N,hb,e,q⟩:=UT ob h Q;rw[e]at P
  have hvj:∀ j,j≠d->v j=0:=λj hj=> by
   have :=P (ah iy 0) j;simp[Uh,Q4,hj,WK.1]at this;exact this
  have as:v d≠0:=λf=> hv (funext λj=> by rcases Y8 j d with rfl | hj;exacts [f,hvj j hj])
  have M:bj (gy iy B (-C)) (single d 1)=(v d)⁻¹•bj (gy iy B (-C)) v:=by
   funext ⟨r,s⟩;by_cases n:s=d
   .subst n;simp[bj];field_simp
   .simp[bj,Q4,n,hvj s n]
  have Py:∀ j,j≠d->Y (0,bn c (rR j))=0:=λj hj=> by
   have :=congrFun (gyr u) j;rw[q]at this;simpa[I8,Q4,hj] using this
  exact gP2 X S hA K d iy Y Y' ⟨y,I2,Kw,Py,G,F,E,p,WK.1,WK.2,
   by rw[M];exact T4 _ _ dm⟩
 ·
  push_neg at h;obtain⟨i,a',b',al,ap,e,q⟩:=UT iy WK z;rw[e]at P
  have k:∀ r,r≠i->w r=0:=λr g=> by
   have :=P r (ah ob 0);simp[Q4,g,XZ,x,h.1]at this;exact this
  have D:w i≠0:=λf=> A (funext λr=> by rcases Y8 r i with rfl | g;exacts [f,k r g])
  obtain⟨Z,hZ,aj⟩:=m
  have ai:=gtm hc (L.map (ig c)) Z (by rwa[Nj c hc])
  have M:bj (gy ob R (-y1)) (single i 1)=dq c ((w i)⁻¹•ig c Z):=by
   rw[S5,gtw hc,aj];funext ⟨r,s⟩;by_cases n:s=i
   .subst n;simp[bj];field_simp
   .simp[bj,Q4,n,k s n]
  have l:∀ (V:Mt) i j,ig c V (i,j)=V (bn c j,bn c i):=λV=> Ip c hc V
  obtain⟨s1,s2⟩:=gts hc G F;obtain⟨s3,s4⟩:=gts hc y I2
  refine gP2 _ ⟨U,T,hc,f,W,J,O7⟩ (e2d T f W J O7).1 K' i ob _ _ ⟨s1,s2,by rw[l,(oq c hc).1,(oq c hc).2.1];exact E,
   λj hj=> ?_,s3,s4,by rw[l,(oq c hc).1,(oq c hc).2.1];exact Kw,
   by rw[l,(oq c hc).2.1];exact u,by rw[l,(oq c hc).2.1];exact h.1,
   by rw[l,(oq c hc).2.1];exact h.2,?_⟩
  · rw[l,(oq c hc).2.2.2,(oq c hc).1]
    have :=congrFun (gyc p) j;rw[q]at this;simpa[o8,Q4,hj] using this
  .simp only[l,(oq c hc).2.1];rw[M];exact S8 (T4 _ _ ai)
 ·
  push_neg at h WK
  have ao:w iy=0:=by
   have :=P iy (ah ob 0);simp[VY,x,XZ,h.1]at this;exact this
  have hvj:v (ah ob 0)≠0:=λf=> A (funext λr=> by
   have :=P r (ah ob 0);simp[f,x,XZ,h.1]at this;exact this)
  have U2:w (ah iy 0)≠0:=λf=> by have :=P (ah iy 0) (ah ob 0);simp[f,Uh,WK.1,hvj]at this
  have Zp:w (ah iy 1)≠0:=λf=> by have :=P (ah iy 1) (ah ob 0);simp[f,UR,WK.2,hvj]at this
  have :=H.2.2.1 _ m _ m;rw[gF2 c ao g0,x,g2]at this;simp[YP hc,U2,Zp,h.1,h.2]at this
lemma gNd {c:Fq} (a:c.val<2) (L:Sq):
 finrank ℂ ↥(Ar (L.map (ig c)) 0 ⊓ iu (L.map (ig c)) c)=finrank ℂ ↥(Ar L 0 ⊓ iu L c):=by
 have k:∀ L:Sq,finrank ℂ ↥(Ar (L.map (ig c)) 0 ⊓ iu (L.map (ig c)) c)≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c):=
  λL=>(Y3 (equivMapOfInjective _ (gtI a) _)).trans_le (W1
   λx d=> by obtain⟨Z,b,rfl⟩:=d;exact gtm a L Z b)
 have :=k (L.map (ig c));rw[Nj c a]at this;exact le_antisymm (k L) this
def ajE L c X (S:gS L c X)
 (a:finrank ℂ ↥(Ar L 0 ⊓ iu L c)=3):False:=by
 obtain⟨m,l,b,k,o,n,j⟩:=id S;obtain⟨f,e,-,d,h,i,g⟩:=gLp S;exact gFL S a.ge (gKE L c X S a)
  (gKE _ c _ ⟨f,e,b,d,h,i,g⟩ (by rw[gNd b L];exact a))
def am9 L c X (S:gS L c X)
 (a:4≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c)):False:=by
 obtain⟨m,l,b,k,o,n,j⟩:=id S;obtain⟨f,e,-,d,h,i,g⟩:=gLp S
 exact gFL S (by omega) (gKN L c X S a)
  (gKN _ c _ ⟨f,e,b,d,h,i,g⟩ (by rw[gNd b L];exact a))
def afO:E2N:=by
 rintro L f h6 c g b e ⟨X,d,a⟩;obtain⟨-,-,i⟩:=e2d h6 b e d a
 rcases (show finrank ℂ ↥(Ar L 0 ⊓ iu L c)=3\/4≤ finrank ℂ ↥(Ar L 0 ⊓ iu L c) by omega) with h | h
 .exact ajE L c X ⟨f,h6,g,b,e,d,a⟩ h
 .exact am9 L c X ⟨f,h6,g,b,e,d,a⟩ h
def ajC:Q7:=abM afX abP afO
end PEqualNP.Outside.L_gct_230
theorem PEqualNP.Outside.L_gct_230 : ¬ (∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L = 6 ∧ ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (if i = j then (2 : ℂ) else 1) + t (i, j)) = 65) := by
  exact PEqualNP.Outside.L_gct_230.ajD PEqualNP.Outside.L_gct_230.apx PEqualNP.Outside.L_gct_230.ajC
