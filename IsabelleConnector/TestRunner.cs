using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace IsabelleConnector;

[TestClass]
public class TestRunner
{
    Executor executor = new Executor(@"C:\Users\emman\Desktop\Isabelle\Isabelle2025");

    [TestMethod]
    public void ExampleValid()
    {
        var proof = """

    value "Var ''x''"
    value "Fun ''one'' []"
    value "Fun ''mul'' [Var ''y'',Var ''y'']"
    value "Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''], Fun ''one'' []]"

    value "Pos ''greater'' [Var ''x'', Var ''y'']"
    value "Neg ''less'' [Var ''x'', Var ''y'']"
    value "Pos ''less'' [Var ''x'', Var ''y'']"
    value "Pos ''equals''
            [Fun ''add''[Fun ''mul''[Var ''y'',Var ''y''], Fun ''one''[]],Var ''x'']"

    fun F⇩n⇩a⇩t :: "nat fun_denot" where
      "F⇩n⇩a⇩t f [n,m] = 
         (if f = ''add'' then n + m else 
          if f = ''mul'' then n * m else 0)"
    | "F⇩n⇩a⇩t f [] = 
         (if f = ''one''  then 1 else
          if f = ''zero'' then 0 else 0)"
    | "F⇩n⇩a⇩t f us = 0"

    fun G⇩n⇩a⇩t :: "nat pred_denot" where
      "G⇩n⇩a⇩t p [x,y] =
         (if p = ''less'' ∧ x < y then True else
          if p = ''greater'' ∧ x > y then True else 
          if p = ''equals'' ∧ x = y then True else False)"
    | "G⇩n⇩a⇩t p us = False"

    fun E⇩n⇩a⇩t :: "nat var_denot" where
      "E⇩n⇩a⇩t x =
         (if x = ''x'' then 26 else
          if x = ''y'' then 5 else 0)"

    lemma "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Var ''x'') = 26" 
      by auto
    lemma "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Fun ''one'' []) = 1" 
      by auto
    lemma "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Fun ''mul'' [Var ''y'',Var ''y'']) = 25" 
      by auto
    lemma 
      "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''], Fun ''one'' []]) = 26" 
      by auto

    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t (Pos ''greater'' [Var ''x'', Var ''y'']) = True" 
      by auto
    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t (Neg ''less'' [Var ''x'', Var ''y'']) = True" 
      by auto
    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t (Pos ''less'' [Var ''x'', Var ''y'']) = False" 
      by auto

    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t 
           (Pos ''equals'' 
             [Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''],Fun ''one'' []]
             ,Var ''x'']
           ) = True" 
      by auto

    definition PP :: "fterm literal" where
      "PP = Pos ''P'' [Fun ''c'' []]"

    definition PQ :: "fterm literal" where
      "PQ = Pos ''Q'' [Fun ''d'' []]"

    definition NP :: "fterm literal" where
      "NP = Neg ''P'' [Fun ''c'' []]"

    definition NQ :: "fterm literal" where
      "NQ = Neg ''Q'' [Fun ''d'' []]"

    theorem empty_mgu: 
      assumes "unifier⇩l⇩s ε L"
      shows "mgu⇩l⇩s ε L"
    using assms unfolding unifier⇩l⇩s_def mgu⇩l⇩s_def apply auto
    apply (rule_tac x=u in exI)
    using empty_comp1 empty_comp2 apply auto
    done

    theorem unifier_single: "unifier⇩l⇩s σ {l}" 
    unfolding unifier⇩l⇩s_def by auto

    theorem resolution_rule':
      assumes "C⇩1 ∈ Cs"
      assumes "C⇩2 ∈ Cs"
      assumes "applicable C⇩1 C⇩2 L⇩1 L⇩2 σ"
      assumes "C = {resolution C⇩1 C⇩2 L⇩1 L⇩2 σ}"
      shows "resolution_step Cs (Cs ∪ C)"
      using assms resolution_rule by auto

    lemma resolution_example1: 
       "resolution_deriv {{NP,PQ},{NQ},{PP,PQ}} 
                                  {{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}}"
    proof -
      have "resolution_step 
              {{NP,PQ},{NQ},{PP,PQ}}
             ({{NP,PQ},{NQ},{PP,PQ}} ∪ {{NP}})"
        apply (rule resolution_rule'[of "{NP,PQ}" _ "{NQ}" "{PQ}" "{NQ}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                  NQ_def NP_def PQ_def PP_def resolution_def
           using unifier_single empty_mgu using empty_subls
           apply auto 
        done
      then have "resolution_step 
              {{NP,PQ},{NQ},{PP,PQ}}
             ({{NP,PQ},{NQ},{PP,PQ},{NP}})" 
        by (simp add: insert_commute) 
      moreover
      have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP}} ∪ {{PP}})"
        apply (rule resolution_rule'[of "{NQ}" _ "{PP,PQ}" "{NQ}" "{PQ}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                  NQ_def NP_def PQ_def PP_def resolution_def
           using unifier_single empty_mgu empty_subls apply auto
        done
      then have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP}})" 
        by (simp add: insert_commute)
      moreover
      have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP},{PP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP}} ∪ {{}})"
        apply (rule resolution_rule'[of "{NP}" _ "{PP}" "{NP}" "{PP}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                  NQ_def NP_def PQ_def PP_def resolution_def
           using unifier_single empty_mgu apply auto
        done
      then have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP},{PP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}})" 
        by (simp add: insert_commute)
      ultimately
      have "resolution_deriv {{NP,PQ},{NQ},{PP,PQ}} 
                             {{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}}"
        unfolding resolution_deriv_def by auto 
      then show ?thesis by auto
    qed

    definition Pa :: "fterm literal" where
      "Pa = Pos ''a'' []"

    definition Na :: "fterm literal" where
      "Na = Neg ''a'' []"

    definition Pb :: "fterm literal" where
      "Pb = Pos ''b'' []"

    definition Nb :: "fterm literal" where
      "Nb = Neg ''b'' []"

    definition Paa :: "fterm literal" where
      "Paa = Pos ''a'' [Fun ''a'' []]"

    definition Naa :: "fterm literal" where
      "Naa = Neg ''a'' [Fun ''a'' []]"

    definition Pax :: "fterm literal" where
      "Pax = Pos ''a'' [Var ''x'']"

    definition Nax :: "fterm literal" where
      "Nax = Neg ''a'' [Var ''x'']"

    definition mguPaaPax :: substitution where
      "mguPaaPax = (λx. if x = ''x'' then Fun ''a'' [] else Var x)"

    lemma mguPaaPax_mgu: "mgu⇩l⇩s mguPaaPax {Paa,Pax}"
    proof -
      let ?σ = "λx. if x = ''x'' then Fun ''a'' [] else Var x"
      have a: "unifier⇩l⇩s (λx. if x = ''x'' then Fun ''a'' [] else Var x) {Paa,Pax}" unfolding Paa_def Pax_def unifier⇩l⇩s_def by auto
      have b: "∀u. unifier⇩l⇩s u {Paa,Pax} ⟶ (∃i. u = ?σ ⋅ i)"
        proof (rule;rule)
          fix u
          assume "unifier⇩l⇩s u {Paa,Pax}"
          then have uuu: "u ''x'' = Fun ''a'' []" unfolding unifier⇩l⇩s_def Paa_def Pax_def by auto
          have "?σ ⋅ u = u"
            proof
              fix x
              {
                assume "x=''x''"
                moreover
                have "(?σ ⋅ u) ''x'' =  Fun ''a'' []" unfolding composition_def by auto
                ultimately have "(?σ ⋅ u) x = u x" using uuu by auto
              }
              moreover
              {
                assume "x≠''x''"
                then have "(?σ ⋅ u) x = (ε x) ⋅⇩t u" unfolding composition_def by auto
                then have "(?σ ⋅ u) x = u x" by auto
              }
              ultimately show "(?σ ⋅ u) x = u x" by auto
            qed
          then have "∃i. ?σ ⋅ i = u" by auto
          then show "∃i. u = ?σ ⋅ i" by auto
         qed
       from a b show ?thesis unfolding mgu⇩l⇩s_def unfolding mguPaaPax_def by auto
    qed

    lemma resolution_example2: 
       "resolution_deriv {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
                                  {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}}"
    proof -
      have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}} ∪ {{Na,Pb}})"
        apply (rule resolution_rule'[of "{Pax}" _ "{Naa,Na,Pb}" "{Pax}" "{Naa}" mguPaaPax ])
           using mguPaaPax_mgu unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
              Na_def Pb_def Nb_def  Pax_def Pa_def Naa_def Paa_def mguPaaPax_def resolution_def
           apply auto
        done
      then have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}})" 
        by (simp add: insert_commute)
      moreover
      have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}} ∪ {{Na}})"
        apply (rule resolution_rule'[of "{Nb,Na}" _ "{Na,Pb}" "{Nb}" "{Pb}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                     Pb_def Nb_def Na_def PP_def resolution_def
           using unifier_single empty_mgu apply auto
        done
      then have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}})" 
        by (simp add: insert_commute)
      moreover
      have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}} ∪ {{}})"
        apply (rule resolution_rule'[of "{Na}" _ "{Pa}" "{Na}" "{Pa}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                      Pa_def Nb_def Na_def PP_def resolution_def
           using unifier_single empty_mgu apply auto
        done
      then have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}})" 
        by (simp add: insert_commute)
      ultimately
      have "resolution_deriv {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}} 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}}"
        unfolding resolution_deriv_def by auto 
      then show ?thesis by auto
    qed

    lemma resolution_example1_sem: "¬eval⇩c⇩s F G {{NP, PQ}, {NQ}, {PP, PQ}}"
      using resolution_example1 derivation_sound_refute by auto

    lemma resolution_example2_sem: "¬eval⇩c⇩s F G {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}"
      using resolution_example2 derivation_sound_refute by auto

    
    """;
        executor.Execute(proof);
    }

    [TestMethod]
    public void ExampleError()
    {
        var proof = """

    value "Var ''x''"
    value "Fun ''one'' []"
    value "Fun ''mul'' [Var ''y'',Var ''y'']"
    value "Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''], Fun ''one'' []]"

    value "Pos ''greater'' [Var ''x'', Var ''y'']"
    value "Neg ''less'' [Var ''x'', Var ''y'']"
    value "Pos ''less'' [Var ''x'', Var ''y'']"
    value "Pos ''equals''
            [Fun ''add''[Fun ''mul''[Var ''y'',Var ''y''], Fun ''one''[]],Var ''x'']"

    fun F⇩n⇩a⇩t :: "nat fun_denot" where
      "F⇩n⇩a⇩t f [n,m] = 
         (if f = ''add'' then n + m else 
          if f = ''mul'' then n * m else 0)"
    | "F⇩n⇩a⇩t f [] = 
         (if f = ''one''  then 1 else
          if f = ''zero'' then 0 else 0)"
    | "F⇩n⇩a⇩t f us = 0"

    fun G⇩n⇩a⇩t :: "nat pred_denot" where
      "G⇩n⇩a⇩t p [x,y] =
         (if p = ''less'' ∧ x < y then True else
          if p = ''greater'' ∧ x > y then True else 
          if p = ''equals'' ∧ x = y then True else False)"
    | "G⇩n⇩a⇩t p us = False"

    fun E⇩n⇩a⇩t :: "nat var_denot" where
      "E⇩n⇩a⇩t x =
         (if x = ''x'' then 26 else
          if x = ''y'' then 5 else 0)"

    lemma "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Var ''x'') = 26" 
      by auto
    lemma "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Fun ''one'' []) = 1" 
      by auto
    lemma "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Fun ''mul'' [Var ''y'',Var ''y'']) = 25" 
      by auto
    lemma 
      "eval⇩t E⇩n⇩a⇩t F⇩n⇩a⇩t (Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''], Fun ''one'' []]) = 26" 
      by auto

    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t (Pos ''greater'' [Var ''x'', Var ''y'']) = True" 
      by auto
    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t (Neg ''less'' [Var ''x'', Var ''y'']) = True" 
      by auto
    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t (Pos ''less'' [Var ''x'', Var ''y'']) = False" 
      by auto

    lemma "eval⇩l E⇩n⇩a⇩t F⇩n⇩a⇩t G⇩n⇩a⇩t 
           (Pos ''equals'' 
             [Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''],Fun ''one'' []]
             ,Var ''x'']
           ) = True" 
      by auto

    definition PP :: "fterm literal" where
      "PP = Pos ''P'' [Fun ''c'' []]"

    definition PQ :: "fterm literal" where
      "PQ = Pos ''Q'' [Fun ''d'' []]"

    definition NP :: "fterm literal" where
      "NP = Neg ''P'' [Fun ''c'' []]"

    definition NQ :: "fterm literal" where
      "NQ = Neg ''Q'' [Fun ''d'' []]"

    theorem empty_mgu: 
      assumes "unifier⇩l⇩s ε L"
      shows "mgu⇩l⇩s ε L"
    using assms unfolding unifier⇩l⇩s_def mgu⇩l⇩s_def apply auto
    apply (rule_tac x=u in exI)
    using empty_comp1 empty_comp2 apply auto
    done

    theorem unifier_single: "unifier⇩l⇩s σ {l}" 
    unfolding unifier⇩l⇩s_def by auto

    theorem resolution_rule':
      assumes "C⇩1 ∈ Cs"
      assumes "C⇩2 ∈ Cs"
      assumes "applicable C⇩1 C⇩2 L⇩1 L⇩2 σ"
      assumes "C = {resolution C⇩1 C⇩2 L⇩1 L⇩2 σ}"
      shows "resolution_step Cs (Cs ∪ C)"
      using assms resolution_rule by auto

    lemma resolution_example1: 
       "resolution_deriv {{NP,PQ},{NQ},{PP,PQ}} 
                                  {{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}}"
    proof -
      have "resolution_step 
              {{NP,PQ},{NQ},{PP,PQ}}
             ({{NP,PQ},{NQ},{PP,PQ}} ∪ {{NP}})"
        apply (rule resolution_rule'[of "{NP,PQ}" _ "{NQ}" "{PQ}" "{NQ}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                  NQ_def NP_def PQ_def PP_def resolution_def
           using unifier_single empty_mgu using empty_subls
           apply auto 
        done
      then have "resolution_step 
              {{NP,PQ},{NQ},{PP,PQ}}
             ({{NP,PQ},{NQ},{PP,PQ},{NP}})" 
        by (simp add: insert_commute) 
      moreover
      have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP}} ∪ {{PP}})"
        apply (rule resolution_rule'[of "{NQ}" _ "{PP,PQ}" "{NQ}" "{PQ}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                  NQ_def NP_def PQ_def PP_def resolution_def
           using unifier_single empty_mgu empty_subls apply auto
        done
      then have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP}})" 
        by (simp add: insert_commute)
      moreover
      have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP},{PP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP}} ∪ {{}})"
        apply (rule resolution_rule'[of "{NP}" _ "{PP}" "{NP}" "{PP}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                  NQ_def NP_def PQ_def PP_def resolution_def
           using unifier_single empty_mgu apply auto
        done
      then have "resolution_step
             {{NP,PQ},{NQ},{PP,PQ},{NP},{PP}}
            ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}})" 
        by (simp add: insert_commute)
      ultimately
      have "resolution_deriv {{NP,PQ},{NQ},{PP,PQ}} 
                             {{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}}"
        unfolding resolution_deriv_def by auto 
      then show ?thesis by auto
    qed

    definition Pa :: "fterm literal" where
      "Pa = Pos ''a'' []"

    definition Na :: "fterm literal" where
      "Na = Neg ''a'' []"

    definition Pb :: "fterm literal" where
      "Pb = Pos ''b'' []"

    definition Nb :: "fterm literal" where
      "Nb = Neg ''b'' []"

    definition Paa :: "fterm literal" where
      "Paa = Pos ''a'' [Fun ''a'' []]"

    definition Naa :: "fterm literal" where
      "Naa = Neg ''a'' [Fun ''a'' []]"

    definition Pax :: "fterm literal" where
      "Pax = Pos ''a'' [Var ''x'']"

    definition Nax :: "fterm literal" where
      "Nax = Neg ''a'' [Var ''x'']"

    definition mguPaaPax :: substitution where
      "mguPaaPax = (λx. if x = ''x'' then Fun ''a'' [] else Var x)"

    lemma mguPaaPax_mgu: "mgu⇩l⇩s mguPaaPax {Paa,Pax}"
    proof -
      let ?σ = "λx. if x = ''x'' then Fun ''a'' [] else Var x"
      have a: "unifier⇩l⇩s (λx. if x = ''x'' then Fun ''a'' [] else Var x) {Paa,Pax}" unfolding Paa_def Pax_def unifier⇩l⇩s_def by auto
      have b: "∀u. unifier⇩l⇩s u {Paa,Pax} ⟶ (∃i. u = ?σ ⋅ i)"
        proof (rule;rule)
          fix u
          assume "unifier⇩l⇩s u {Paa,Pax}"
          then have uuu: "u ''x'' = Fun ''a'' []" unfolding unifier⇩l⇩s_def Paa_def Pax_def by auto
          have "?σ ⋅ u = u"
            proof
              fix x
              {
                assume "x=''x''"
                moreover
                have "(?σ ⋅ u) ''x'' =  Fun ''a'' []" unfolding composition_def by auto
                ultimately have "(?σ ⋅ u) x = u x" using uuu by auto
              }
              moreover
              {
                assume "x≠''x''"
                then have "(?σ ⋅ u) x = (ε x) ⋅⇩t u" unfolding composition_def by auto
                then have "(?σ ⋅ u) x = u x" by auto
              }
              ultimately show "(?σ ⋅ u) x = u x" by auto
            qed
          then have "∃i. ?σ ⋅ i = u" by auto
          then show "∃i. u = ?σ ⋅ i" by auto
         qed
       from a b show ?thesis unfolding mgu⇩l⇩s_def unfolding mguPaaPax_def by auto
    qed

    lemma resolution_example2: 
       "resolution_deriv {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
                                  {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}}"
    proof -
      have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}} ∪ {{Na,Pb}})"
        apply (rule resolution_rule'[of "{Pax}" _ "{Naa,Na,Pb}" "{Pax}" "{Naa}" mguPaaPax ])
           using mguPaaPax_mgu unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
              Na_def Pb_def Nb_def  Pax_def Pa_def Naa_def Paa_def mguPaaPax_def resolution_def
           apply auto
        done
      then have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}})" 
        by (simp add: insert_commute)
      moreover
      have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}} ∪ {{Nb}})"
        apply (rule resolution_rule'[of "{Nb,Na}" _ "{Na,Pb}" "{Nb}" "{Pb}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                     Pb_def Nb_def Na_def PP_def resolution_def
           using unifier_single empty_mgu apply auto
        done
      then have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Nb}})" 
        by (simp add: insert_commute)
      moreover
      have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}} ∪ {{}})"
        apply (rule resolution_rule'[of "{Na}" _ "{Pa}" "{Na}" "{Pa}" ε])
           unfolding applicable_def vars⇩l⇩s_def  vars⇩l_def 
                      Pa_def Nb_def Na_def PP_def resolution_def
           using unifier_single empty_mgu apply auto
        done
      then have "resolution_step 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}}
             ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}})" 
        by (simp add: insert_commute)
      ultimately
      have "resolution_deriv {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}} 
              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}}"
        unfolding resolution_deriv_def by auto 
      then show ?thesis by auto
    qed

    lemma resolution_example1_sem: "¬eval⇩c⇩s F G {{NP, PQ}, {NQ}, {PP, PQ}}"
      using resolution_example1 derivation_sound_refute by auto

    lemma resolution_example2_sem: "¬eval⇩c⇩s F G {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}"
      using resolution_example2 derivation_sound_refute by auto
    
    """;
        executor.Execute(proof);
    }
}
