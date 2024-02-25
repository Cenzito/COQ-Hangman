Require Import String.
Require Import Ascii.
Require Import List.
Require Import ssreflect ssrbool.
 
Print In.

(* ------COQ PROJECT BY OSCAR PEYRON AND CENZO POIRIER DE CARVALHO------ *)
(* 
  The goal of this project is to implement a helper for crosswords that takes
  as input an incomplete word (i.e., a word with some unknown letters)
  and returns the list of matching complete words together with their 
  definitions. For example, given as input t-b-, the helper returns the words
  tube, tuba, tabu, along with their definitions.

  The first challenge consists in defining a data structure that can represent
  efficiently the dictionary.

*)

Definition char := ascii.


(*

A string is esentially a list of characters: it is a datatype with two
constructors: one denoting the empty list, and the other appending a character
to an existing string.
 *) 
Print string.
(*
   Inductive string : Set :=
    EmptyString : string
|   String : ascii -> string -> string.
*)


Open Scope string_scope.

(*

Double quotes denote strings, unless they are postfixed with %char, in
which case they denote single characters.

 *)
Check ("f"%char : char).
Check ("string example" : string).

(* Equality of chars *)
Infix "=c" := Ascii.eqb (at level 70).

(* false *)
Eval compute in ("c"%char =c "d"%char).
(* true *)
Eval compute in ("c"%char =c "c"%char).

(*

A dictionary is a tree whose nodes are possibly labelled by a string,
and edges are labelled by characters.

Each node represents a list of characters obtained by concatenating the labels along the
path from the root to itself. If this list of characters is actually a word,
the node is labelled with its definition.


 *)

Inductive Dictionary := 
     Entry : option string -> ListDictionary -> Dictionary
with ListDictionary :=
     Empty : ListDictionary
   | Cons : ListDictionary -> char -> Dictionary -> ListDictionary.

(*

For example, the dictionary containing the words "that", "the", "then" is represented by
the tree (unlabelled nodes are denoted by -)
                   -
                   |t
                   -
                   |h
                   -
                  / \
               a /   \ e
                /     \
               -      "denoting person(s) or thing(s) already mentioned"
              /          \ 
             /            \ n 
          t /              \
           /            "next; after that."
          /
  "1 person or thing indicated, named, or understood"



 *)
(*
---------
Exercise 
---------
Define the empty dictionary

 *)
Print option.

Definition empty : Dictionary := Entry None Empty. (* None = option string, Empty = ListDictionnary) *) 

(*
---------
Exercise 
---------

Define the dictionary containing "that", "the", "then", as drawn above

*)
Definition that_the_then : Dictionary := 
(Entry None (Cons Empty "t"%char (Entry None (Cons Empty "h"%char 
(Entry None (Cons (Cons Empty "a"%char (Entry None (Cons Empty "t"%char 
(Entry (Some "1 person or thing indicated, named, or understood") Empty)))) "e"%char 
(Entry (Some "denoting person(s) or thing(s) already mentioned") 
(Cons Empty "n"%char (Entry (Some "next; after that.") Empty))))))))).



(*

---------
Exercise 
---------

Define a 'find' function  that takes as input a word, a dictionary, and
return the associated definition in the dictionary, or None
if the word does not exist.


*)



(* find INPUT: WORD, DICTIONNARY --> DEFINITION*) 

Fixpoint find (word : string) (dictionary : Dictionary) : option string :=

 match word with (*case over the word *) 
  |EmptyString =>
    match dictionary with (* case over the dictionary *) 
    |Entry str listd => str  (*returns the def *) 
    end
  |String a b=>  (* if the word is String a b*) 
    match dictionary with
    |Entry str listd => (find_list a b listd)  (*we see if such a word exist in the listdictionnary *) 
    end
  end

with find_list char word listDictionary : option string :=
   match listDictionary with 
  |Empty => None (* if the listdictionnary is empty then the word does not exist and hence no def*) 
  |Cons LD ch D => 
  if ch =c char then (find word D) (* if the char matches try to find the definition in the dicitonnary associated *) 
  else (find_list char word LD)
  end.

(* Your function should return the definitions  *)
Eval compute in find "that" that_the_then .
Eval compute in find "the" that_the_then .
Eval compute in find "then" that_the_then .
(* Your function should return None *)
Eval compute in find "them" that_the_then .

(*

---------
Exercise 
---------

Define a 'new' function that takes as input a word, a definition, 
and returns dictionary containing this single word with its definition.

Test your function with the 'find' function and the 'Eval compute'
command as above.

*)


(* NEW : INPUT : WORD, DEFINITION , --> DICTIONNARY *)
 
Fixpoint new (word : string) (def : string) := 
  match word with
  |EmptyString => (Entry (Some def) Empty) (* defining the EmptyString is all we need so the rest is Empty*)
  |String ch str => (Entry None (Cons Empty ch (new str (def)))) (* induction here with new str*) 
  end.

Eval compute in (find "the" (new "the" ("this thing"))).
 


(*
---------
Exercise 
---------

Define an 'insert' function that takes as input a word, a definition, 
a dictionary, and returns a dictionary extending the previous one with the
new definition given as input.

.
*)

(* INSERT : INPUT : WORD, DEF, DICTIONNARY --> DICTIONNARY *) 

 Fixpoint insert word (def:string) dictionary :=
  match dictionary with (*case of dictionnary *) 
  |Entry ostr LoD =>
    match word with
    |EmptyString => (Entry (Some def) LoD) (*define the EmptyString and leave the rest the same *)
    |String a b => (Entry ostr (insert_list a b def LoD)) (* now insert the def in the listOfdictionnary*) 
    end
  end
with insert_list char word def listDictionary :=
  match listDictionary with
  |Empty => (Cons Empty char (new word def)) (*since char is not in this level, we can just add the rest i.e char + new word def at this level *)
  |Cons LD c D =>
    if (c =c char) then (Cons LD c (insert word def D)) (* decreases the size of word by 1 which is essential*)
    else (Cons (insert_list char word def LD) c D) (* keep looking for the matching character if there's more *)
end.

(* **************

Now we are going to prove that these functions are correct.

************  *)

(*
--------
Exercise
--------
*)
Lemma find_empty word :
  find word empty = None.  (*if Dictionnary empty there is nothing to find --> NONE *) 
Proof.
case word. simpl. done. done.
Qed.


(*
--------
Exercise
--------
*)



(*eqb_refl: forall x : ascii, (x =c x) = true*)

Lemma find_create def word :
  find word (new word def) = Some def. (* if (new word def) extends the dictionnary with a definition,
                                         finding the word assocaited to that definition gives you the defintion --> SOME DEF *) 
Proof.
induction word. done. simpl. rewrite (eqb_refl a). apply IHword. 
Qed.


(*
--------
Exercise
--------
*)


(*eqb_eq:
  forall n m : ascii, (n =c m) = true <-> n = m*) 

Lemma help_find_create_unique (def:string) (def':string) (word:string) :
  forall word', find word' (new word def) = Some def' ->
  def = def' /\ word = word'. (* UNICITY OF THE (WORD, DEF) in a dictionnary  *)
Proof.
induction word. simpl. move=> word'. case word'. move=> a. inversion a.
split; done. done. move=> b. case b. simpl. done. move=> ch wor. simpl.
case e: (a =c ch)%char. apply eqb_eq in e. rewrite e. move=> f. apply (IHword wor) in f.
split. case f=> [g h]. apply g. case f=> [g h]. rewrite h. done. done.
Qed.


(*def = def' /\ String a word = word'*) 
(* f : f : find wor (new word def) = Some def'*) 

Lemma find_create_unique def def' word word' :
  find word' (new word def) = Some def' ->
  def = def' /\ word = word'.
Proof.
apply (help_find_create_unique def def' word). (*particular case *)
Qed.



(*
--------
Exercise
--------
*)

Search eqb.

(*eqb_neq:
  forall x y : ascii, (x =c y) = false <-> x <> y*) 


Lemma help_find_create_none def word: (* COROLLARY OF THE PREVIOUS LEMMA *) 
  forall word', word <> word' ->
   find word' (new word def) = None. (* you cannot two different words in a dictionnary that only contains one *) 
Proof.
unfold find.
induction word. simpl. move=> word'. case word'. done. done. simpl. move=> word'. case word'. done. move => ch s.
case e: (a =c ch)%char. simpl. apply eqb_eq in e. rewrite e. move=> b.
apply (String.eqb_neq (String ch word) (String ch s)) in b. simpl in b. 
rewrite (Ascii.eqb_refl ch) in b. apply (String.eqb_neq (word) (s)) in b. revert b.
apply (IHword s). done.
Qed.

Search "=?".
Corollary find_create_none def word word' : word <> word' -> 
   find word' (new word def) = None.
Proof.
apply (help_find_create_none def word). (*particular case *) 
Qed.


Scheme Dictionary_List_rec := Induction for Dictionary Sort Prop
  with ListDictionary_Dictionary_rec := Induction for ListDictionary Sort Prop.

Combined Scheme CombinedDictionary_rec from Dictionary_List_rec, ListDictionary_Dictionary_rec.
(*

The dictionary data structure comes with an induction principle called
Dictionary_List_rec.
When you want to prove a property P about dictionaries, you first need to define
a similar property P0 about list of dictionaries (ListDictionary) that you
will show by induction.

*)
Check Dictionary_List_rec.


Lemma find_add : forall dictionary def word,
   find word (insert word def dictionary) = Some def. (*finding the definition of a word in a dictionnary in which the def was inserted gives you the defintion *) 
Proof.
induction dictionary using Dictionary_List_rec with (P0 := fun listDictionary => (* using the Combined Scheme *)
forall char word def, (find_list char word (insert_list char word def listDictionary) = Some def)).
move=> def word. case word. simpl. done. simpl. move => a s. apply (IHdictionary a s def).
simpl. move => ch. rewrite (Ascii.eqb_refl ch). move => word def.
apply find_create. simpl. move=> ch word def . case e: (c =c ch)%char.
simpl. rewrite e. apply IHdictionary0. simpl. rewrite e. apply IHdictionary.
Qed.


(*
--------
Exercise
--------
*)
Lemma find_add' : forall dictionary def word word', word <> word' ->
   find word' (insert word def dictionary) = 
     find word' dictionary. (* the insertion of a defintion which has no link with the word with want to change do not change the output of the find result *) 
Proof.      
induction dictionary using Dictionary_List_rec with (P0 := fun listDictionary => 
forall char char' word word' def,  String char word <> String char' word' -> (find_list char' word' (insert_list char word def listDictionary) =
(find_list char' word' listDictionary))).
move=> def word word'. case word. case word'. simpl. done. simpl. done.
simpl. case word'. done. move=> a s a0 s0. 
 apply (IHdictionary a0 a s0 s).
move=> char char' word word' def. simpl. case e: (char =c char')%char. move=> b.
apply (String.eqb_neq (String char word) (String char' word')) in b. simpl in b.
rewrite e in b. apply (String.eqb_neq (word) (word')) in b. revert b.
apply find_create_none. done. simpl. move => char char' word word' def.
case e: (c =c char)%char; case f: (c =c char'). simpl.
rewrite f. move=> b. apply (String.eqb_neq (String char word) (String char' word')) in b.
simpl in b. apply eqb_eq in e. symmetry in e. rewrite e in b. rewrite f in b. 
apply (String.eqb_neq (word) (word')) in b.
revert b. apply IHdictionary0 .
simpl. rewrite f. done. simpl. rewrite f. done. 
simpl. rewrite f. apply IHdictionary.
Qed.



  
(* 

For some proofs, we will need to make explicit that the dictionnaries built
only through add have some canonicity: namely that in a ListDictionnary, a 
letter occurs at most once.

In other words, the following Dictionnary is not canonical because there are
two entries for the letter t at the same level

Definition twice_t : Dictionary :=
  Entry None
  (Cons  (Cons Empty "t"%char
               (Entry None (Cons Empty "h"%char 
                                 (Entry None
                                        (Cons Empty "e"%char
                                              (Entry (Some "definition of the")
                                                     Empty))))
               )
         ) "t"%char
         (Entry None
                (Cons Empty "o"%char
                      (Entry (Some "definition of to") Empty)))
  ).



*)


(* Notoccur : INPUT : char, list --> Boolean *) 

Fixpoint notoccur c l :=
  match l with
  | Empty => True (* c is obviously not in Empty, in fact, no character is *)
  | Cons l c' _ => ~(c =c c') /\ notoccur c l (* if c is not equal to c' and notoccur c inside l is True --> recursion *) 
  end.


(*
--------
Exercise
--------
*)
(* Possibly using notoccur, define the predicate specifying that such a situation like 
twice_t does not happen in a Dictionary (resp. a DictionaryList *)



(* CANONICAL : INPUT : DICTIONNARY --> BOOLEAN *) 
Fixpoint canonical d :=
  match d with
  |Entry ostr LD => canonical_l LD (* check the LD*)
  end
with
canonical_l l :=
  match l with
  |Empty => True (* an empty LD counts as being canonical since nothing is repeated *)
  |Cons LD ch D => (notoccur ch LD) (*char cannot be already in LD*) 
                    /\ (canonical_l LD) (*LD does not contain two of the same character at the same level *) 
                     /\ (canonical D) (*make sure the property holds for further layers*) 
end.



(* Show a dictionary built by new is always canonical *)

Lemma new_canonical : forall w d, canonical (new w d). 
Proof.
move => word dic. induction word. simpl. done. simpl. split. done. split. done. apply IHword.
Qed.




(*
--------
Exercise
--------
*)
(* Now show that the canonical property is preserved by insert *)

(* Show that if two char are different if you insert one in the list_dictionnary 
and the other one is not in the list dictionnary 
then the second char won't be found in the list_dictionnary *) 

Lemma ntoc :
forall c c' word l def , notoccur c l /\ ~(c =c c')%char -> notoccur c (insert_list c' word def l).
Proof.
move=> c c' word l def. induction l. simpl. move=> a. case a=> [b d]. split; assumption.
move=> [e f]. simpl. case g:(c0 =c c')%char. simpl. split.  apply (Ascii.eqb_eq c0 c') in g.
symmetry in g. rewrite g in f. exact f. simpl in e. case e=> [x y]. exact y. simpl.
simpl in e. case e=> [x y]. split. exact x. apply IHl. split. exact y. exact f.
Qed.



Lemma insert_canonical : forall d w def, canonical d -> canonical (insert w def d).
Proof.

induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall ch w def, (canonical_l listDictionary) -> (canonical_l (insert_list ch w def listDictionary))).
simpl. move=> word def . move=> a. case word. simpl. exact a.
simpl. move=> a0 s. apply IHd. exact a. simpl. move=> a word def. move=>b.
split; try split; try done. apply new_canonical.
simpl. move=> ch word def. case z: (c =c ch)%char.
move=> a. simpl. split; try split. case a=> [e f]. exact e. 
case a=> [e f]. case f=> [g h]. apply g. apply IHd0.
case a=> [e f]. case f=> [g h]. exact h.
simpl. move => a. case a=> [b [e f]]. split; try split.  apply ntoc. split.
exact b.  rewrite z. compute. done. apply IHd. exact e. exact f.
Qed.




(*
--------
Exercise
--------
 *)
(* translate a list of definitions into a Dictionary *)
Print list.



(* dict_from_list : INPUT : list(string * stirng) --> Dictionnary*)

Fixpoint dict_from_list (l : list (string * string)) : Dictionary :=
match l with 
|nil => empty (* a dictionary containing no words is empty *)
|cons A l => (insert (fst A) (snd A) (dict_from_list l)) (* go one element by one and induction *)
end.


(* A quiz corresponds to a situation in the Hangman game, that is
a word of whom some letters are known, as well as its length. For instance 
  "hang_a_" of "h_n_m_a" *)
Definition quiz := list (option char).



(*
--------
Exercise
--------
*)

(* string_to_quiz : INPUT STRING --> OPTION CHAR *) 
Definition string_to_quiz (s : string) : list (option char) :=
  List.map (fun c => if c =c "-" then None else Some c) 
  (list_ascii_of_string s).

Eval compute in (string_to_quiz "ab-").


(*
--------
Exercise
--------
*)

(* Define the property that a string (like "hagnman")
   fits a quiz (like h_ngman) *)

Fixpoint fits (s:string) (q:quiz) :=
  match q with (*case on the quiz*)
  |nil=> 
    match s with
      |EmptyString => true (* EmptyString fits the quiz containing nothing *)
      |String a b=> false (* any other word doesn't fit*)
    end
  |cons b l' =>
    match s with
      |EmptyString => false (* the EmptyString can't fit a quiz of length at least 1 *)
      |String ch str =>
        match b with
        |None =>  (fits str l') (*if None then any character can fit so we check the rest of the string *)
        |Some c=> (c =c ch) && (fits str l') (*we check if the character fits and the rest fits*)
        end
      end
 
      
end.



Eval compute in (fits ("abc") (string_to_quiz "ab-")).


Definition appString s c :=
  String.append s (String c "").

(*
--------
Exercise
--------
*)

(* Define a fuction enumerating all the words of a Dictionary which fit a given quiz *)
Print String.
Print list.


(* enum_aux : INPUT : QUIZ, DICTIONARY, LIST STRING, STRING --> LIST STRING*) 
Fixpoint enum_aux (q : quiz)(d : Dictionary)(found : list string)(cur : string) : list string :=

  match d with (*case on dictionary*)
  | Entry o LD => 
    match o with 
    | Some definition => 
       if (fits cur q) then cons cur found (*if the current word has a definition and fits then it is valid
                                            and we add it to the list. furthermore, if we kept going the word would get longer, i.e not fit 
                                            in the quiz so we stop here for this branch.*)
       else (enum_l_aux q LD found cur) (*otherwise keep going*)
     | None => (enum_l_aux q LD found cur) (*this word has no definition, it can't be valid so we keep looking*)
     end
   end

with enum_l_aux q l found cur :=
  match l with
    | Empty => found (*there is nothing else to find*)
    | Cons ld char D => (enum_aux q D nil (appString cur char)) ++ (enum_l_aux q ld found cur) (*return the valid words from both sides without doubles as long as canonical*)

end.

(* l listDictionnary,*) 


(*ENUM INPUT : QUIZ, DICTIONARY --> LIST STRING *)
Definition enum (q : quiz) (d : Dictionary) : list string :=
  (enum_aux q d nil "").




(* Test your function *)
Definition d1 :=
  insert "abo" "o" 
         (insert "aba" "a" (Entry None Empty)) .

Eval compute in (enum (cons None (cons (Some "c"%char) (cons (Some "o"%char) nil)))
                      d1).

Eval compute in (enum (cons None (cons (None) (cons (Some "a"%char) nil)))
                      d1).

Eval compute in (fits ("aba") (cons None (cons (None) (cons (Some "a"%char) nil)))).

Eval compute in (enum (cons (Some "a"%char) (cons (Some "b"%char) (cons None nil)))
                      d1).

(* we used more complex examples for testing the enum *)
Definition test_dict_enum := 
  (insert "coq" "the best programming language"
  (insert "tame" "some def of tame"
  (insert "then" "Some def of then"
  (insert "thus" "Some definition of thus" 
    (insert "the" "Some definition of the" 
      (insert "thee" "Some def of thee"
        (insert "these" "Some def of these"
          (insert "they" "some def of they"
      (new "that" "some definition of that"))))))))).

Definition test_quiz :=
  string_to_quiz "---".

(*as we can see it works fine*)
Eval compute in (enum test_quiz test_dict_enum).

(* Helping lemma *) 
Lemma string_app_nil :
  forall w, w++"" = w.
Proof.
by elim => [//=| c w /= ->]. 
Qed.
Search String.

Lemma string_app_app : forall a b c, appString a c ++ b=a ++ String c b  .
Proof.
elim => [//=|d a ha]//= b c.
by rewrite ha.
Qed.


Lemma notoccur_None :  forall l c w, notoccur c l -> find_list c w l = None.
Proof.
induction l; simpl. done.
move => c' w  ; case e: eqb; simpl; case; auto. done.  rewrite eqb_sym in e. rewrite e. auto.
Qed.

(*
--------
Exercise
--------
*)
(* The two following lemmas state that the enum function is correct *)
(* The important step for you will be to state the generalized correction
   properties verified by your recursive functions (the enum_aux and 
   enum_l_aux functions; these will be the properties that can be shown
   by mutual induction *)




(*Helper Lemmas--------------------------------------------------------------*) 

Lemma app3 : forall ch c curr,
(appString (String c curr) ch) = String c (appString curr ch).
Proof.
intros. rewrite <- (string_app_nil (appString (String c curr) ch)).
rewrite (string_app_app (String c curr) "" ch). simpl. symmetry.
rewrite <- (string_app_nil (appString curr ch)). rewrite string_app_app. done.
Qed.


Lemma concfalse : forall curr ch s,
(curr <> curr ++ String ch s).
Proof.
intros curr ch s. induction curr as [| c curr IHcurr]. simpl. 
done. move => [e]. apply IHcurr. done. 
Qed.

Lemma asso : forall (a:string) b c,
(a++b)++c=a++(b++c).
Proof.
intros. induction a. simpl. done. simpl. rewrite IHa. done.
Qed.

Lemma asso2 : forall curr ch ext,
curr++(String ch ext)=curr++(String ch "" )++ ext.
Proof.
move=> curr. induction curr. simpl. done.
 simpl. simpl in IHcurr. move=> ch ext. done.
Qed.

Lemma incfal2 : forall d curr q ch s,
(In (curr) (enum_aux q d nil (curr ++ (String ch s))))-> False.
Proof.
induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall curr ch q s, In (curr) (enum_l_aux q listDictionary nil (curr ++ (String ch s))) -> False).
intros. revert H. simpl. case o. case (fits (curr ++ String ch s) q). simpl. intros. 
case H. induction curr.
simpl. move=> g. symmetry in g.  done.
move=> e. symmetry in e. apply concfalse in e. done. done.
move=> str. apply IHd. apply IHd. simpl. done.
simpl. intros. apply in_app_or in H. case: H.

rewrite <- (string_app_nil (appString (curr ++ String ch s) c)).
rewrite (string_app_app (curr ++ String ch s) "" c).
rewrite (asso curr (String ch s) (String c "")).
apply (IHd0 curr q ch (s ++ String c "")).
apply IHd.
Qed.


Lemma incurrenumlfalse : forall curr q l,
(In curr (enum_l_aux q l nil curr))-> False.
Proof.
move => curr q l. induction l. simpl. done. simpl. move=> k. apply in_app_or in k.
case: k. rewrite <- (string_app_nil (appString curr c)).
rewrite (string_app_app). apply (incfal2 d curr q c ""). apply IHl.
Qed.


Lemma extracurr : forall d q curr s s' ch c,
ch<>c -> (In (curr ++ (String c s)) (enum_aux q d nil (curr++(String ch s'))))->False.
Proof.
induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall curr s s' q c ch, 
ch<>c-> 
(In (curr++(String c s)) (enum_l_aux q listDictionary nil (curr++(String ch s')))) 
-> False).
simpl. case o. intros. revert H0. case (fits (curr ++ String ch s') q).  induction curr. simpl.
 move=> k. case k. move=>g. move: g=> [h]. done. done.
simpl.
simpl in IHcurr. move=> [p|r]. move: p=>[t]. case IHcurr. left. done. done.
simpl. apply IHd. exact H. intros. apply (IHd curr s s' q c ch). exact H. exact H0.
simpl. done.
simpl. intros. apply in_app_or in H0. case: H0.
simpl. rewrite <- (string_app_nil (appString (curr ++ String ch s') c)).
rewrite string_app_app. rewrite asso. simpl.
apply (IHd0 q curr s (s' ++ String c "") ch c0). exact H.  apply IHd. exact H.
Qed.

Search eqb.

Lemma find_enum_nild : forall d curr ext q,
canonical d->find ext d = None->
In (curr ++ ext) (enum_aux q d nil curr) -> False.
Proof.
induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall curr ch ext q, canonical_l listDictionary -> find_list ch ext listDictionary = None 
-> In (curr++(String ch ext)) (enum_l_aux q listDictionary nil (curr)) -> False).
simpl. move=> curr ext q canl. case ext. rewrite string_app_nil. move=> e. rewrite e.
apply incurrenumlfalse. move=> a s fl. case o. case (fits curr q). simpl.
intros. case H. apply concfalse. done. move=>str. 
apply (IHd curr a s q). exact canl. apply fl. apply IHd. exact canl. exact fl.
simpl. done.
simpl. move=> curr ch ext q [x [y z]]. case g: (c =c ch). intros. 
apply in_app_or in H0. case: H0. revert H. rewrite <- (string_app_nil (appString curr c)).
rewrite string_app_app. apply eqb_eq in g. rewrite g.
rewrite asso2. rewrite <- asso.  
apply (IHd0 (curr++(String ch "")) ext q). exact z. apply IHd. exact y.
apply notoccur_None. apply eqb_eq in g. rewrite g in x. apply x.
simpl. intros. apply in_app_or in H0. case: H0. move=>k.
rewrite <- (string_app_nil (appString curr c)) in k.
rewrite (string_app_app curr "" c) in k. apply eqb_neq in g. 
apply (extracurr d q curr ext "" c ch). exact g.
exact k. apply IHd. exact y. exact H.
Qed.


Lemma find_enum_nil : forall l curr ch ext q,
canonical_l l -> (find_list ch ext l = None) ->  (In (appString curr ch ++ ext) (enum_l_aux q l nil curr))->False.
Proof.
move=> l. induction l. move=> curr ch ext q .  simpl. done. simpl.
move=> curr ch ext q. case e: (c =c ch).
move=>[no [canl cand]] g h. apply in_app_or in h. case: h.
apply eqb_eq in e. rewrite e. 
rewrite (string_app_app curr ext ch). 
rewrite <- (string_app_nil (appString curr ch)).
rewrite (string_app_app). rewrite (asso2 curr ch ext).
rewrite <- (asso curr (String ch "") ext).
apply (find_enum_nild d (curr ++ String ch "") ext q). exact cand.  exact g.
apply IHl. exact canl. apply (notoccur_None l c ext) in no. apply eqb_eq in e. rewrite e in no. exact no.
move=> [no [canl cand]]. intros. apply in_app_or in H0. case: H0.
rewrite (string_app_app). rewrite <- (string_app_nil (appString curr c)).
rewrite string_app_app. apply (extracurr d q curr ext "" c ch).
move=> j. apply eqb_eq in j. rewrite e in j. done. apply IHl. exact canl. exact H.

Qed.



Lemma ineq_not_in : forall d curr ch c ext q ,
((c =c ch) = false)->(In (appString curr ch ++ ext) (enum_aux q d nil (appString curr c)))->False.
Proof.
induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall curr ch c ext q, ((c =c ch) = false)->
In (appString curr ch ++ ext) (enum_l_aux q listDictionary nil (appString curr c))-> False).

move=> curr ch c ext q.
simpl. case o. case (fits (appString curr c) q). move=> str.
move=> a. simpl. move=> [b|e]. revert b. case ext. rewrite string_app_nil. induction curr.
move=>b. rewrite <- (string_app_nil (appString "" c)) in b.  rewrite (string_app_app ) in b.
symmetry in b. rewrite <- (string_app_nil (appString "" ch)) in b.  rewrite (string_app_app ) in b.
simpl in b. 

move: b => [e].
by rewrite e eqb_refl in a. simpl. rewrite app3. move=> r. symmetry in r.
rewrite app3 in r. move:r=>[k]. symmetry in k. apply IHcurr in k. done. induction curr.
simpl. intros. rewrite <- (string_app_nil (appString "" c)) in b. rewrite string_app_app in b.
simpl in b. move: b=> [e]. simpl. move=>j. apply eqb_eq in e. rewrite a in e. done.
intros. rewrite app3 in b. symmetry in b. rewrite app3 in b. simpl in b. move: b=>[f].
symmetry in f. apply IHcurr in f. done. done. simpl. intros. apply (IHd curr ch c ext q). exact H.
exact H0. apply IHd. simpl. done. 

simpl. intros. apply in_app_or in H0. case: H0.  move=> k.
apply (extracurr d q curr ext (String c "") c0 ch). move=> j. 
apply eqb_eq in j.
rewrite H in j. done. rewrite (string_app_app curr ext ch) in k.
rewrite <- (string_app_nil (appString curr c0)) in k.
rewrite (string_app_app curr "" c0) in k.
rewrite <- (string_app_nil (appString (curr ++ String c0 "") c)) in k.
rewrite (string_app_app (curr ++ String c0 "") "" c) in k.
rewrite asso in k. simpl in k. exact k.
revert H. apply IHd.

Qed.

Lemma fitplus : forall curr q a s,
(fits curr q)-> (fits (curr ++ String a s) q) -> False.
Proof.
induction curr. simpl. move=> q a s. case q. done. simpl. done.
simpl. move=> q a0 s. case q. done. move=> o l. case o.
move=> c. case e: (c =c a). simpl. apply IHcurr. simpl. done. 
apply IHcurr.
Qed.

(*
We used this function in some of the following proofs:
in_or_app:
  forall [A : Type] (l m : list A) (a : A), In a l \/ In a m -> In a (l ++ m)
*)

(** MAIN HELPER LEMMAS **)
Lemma dic_enum_fit_aux : forall d q curr ext,
canonical d -> 
In (curr++ext) (enum_aux q d nil curr) ->
exists def, find ext d = Some def /\ fits (curr++ext) q.
Proof.

induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall ch q curr ext, (canonical_l listDictionary) -> 
In (curr++(String ch ext)) (enum_l_aux q listDictionary nil curr)->
exists def, (find_list ch ext listDictionary)=Some def /\ (fits (curr++(String ch ext)) q)).
move=> q curr ext canl. simpl. case o. case ext. case e: (fits curr q). move=>s.
rewrite string_app_nil. simpl. move=> a. exists s. done. move=>s. rewrite string_app_nil.
move=> f. apply incurrenumlfalse in f.  done. move=> a s str. case e: (fits curr q). simpl. move=>b.
case b. move=> g. apply concfalse in g. done. done. apply IHd. apply canl.  case ext.
rewrite string_app_nil. move=> e. apply incurrenumlfalse in e. done. move=> ch s.
move=>b. apply IHd. apply canl. apply b. move=> ch q curr ext. simpl. done. 
move=> ch q curr ext. simpl. move=> [x [y z]]. case f:(c=?ch)%char. apply eqb_eq in f.
rewrite f. rewrite <- string_app_app. move=> a. apply (IHd0 q (appString curr ch) ext).
apply z.  apply (in_app_or (enum_aux q d nil (appString curr ch))
 (enum_l_aux q l nil curr) (appString curr ch ++ ext)) in a. case a=> [g|h]. apply g.
apply (notoccur_None l c ext) in x. rewrite f in x. 


 apply (find_enum_nil l curr ch ext q) in x. 
done. exact y. exact h.
move=> b. apply IHd. apply y. rewrite <- string_app_app in b. apply (in_app_or (enum_aux q d nil (appString curr c))
 (enum_l_aux q l nil curr) (appString curr ch ++ ext)) in b. case b=> [g|h]. 
apply (ineq_not_in d curr ch c ext q ) in f.  done. exact g. rewrite <- string_app_app.
done.
Qed.

Lemma enum_complete_aux : forall d q curr ext,
fits (curr++ext) q ->
(exists def, find ext d = Some def) ->
In (curr++ext) (enum_aux q d nil curr).
Proof.
induction d using Dictionary_List_rec with (P0 := fun listDictionary => 
forall ch a q curr ext, fits (curr++(String ch ext)) (cons a q) ->
(exists def, (find_list ch ext listDictionary) = Some def) ->
In (curr++(String ch ext)) (enum_l_aux (cons a q) listDictionary nil curr)).


move=> q curr ext. simpl. case ext. case o. move=> s. rewrite string_app_nil. case e: (fits curr q).
intros. simpl. left. done. done. rewrite string_app_nil. intros. case H0. done.
move=> a s. case o. case e: (fits curr q). move=> str fitsplus. apply (fitplus curr q a s) in e. 

done. apply fitsplus.
move=> str. case q. simpl. case curr. simpl. done. simpl. done. intros. apply IHd. exact H. exact H0.
case q. case curr. simpl. done. simpl. done. intros; apply IHd. exact H. exact H0.


move=> ch a q curr ext. simpl. intros. case H0. done. 

move=> ch a q curr ext. simpl. case e: (c =c ch). move=> b f. apply in_or_app. left. apply eqb_eq in e. rewrite e.
rewrite <- string_app_app. apply IHd0. rewrite <- (string_app_app curr ext ch) in b. exact b. exact f.

intros. apply in_or_app. right. apply IHd. exact H. exact H0.


Qed.

(*END OF Helper Lemmas---------------------------------------------------*) 

(*FINAL LEMMAS --------------------------------------------------------*)


Lemma dic_enum_fit : forall d q w, canonical d -> 
    In w (enum q d) ->
    exists def, find w d = Some def /\ fits w q.
Proof.
move=> d q w.
apply (dic_enum_fit_aux d q "" w).
Qed.




Lemma enum_complete : forall d q w, fits w q ->
                                    (exists def, find w d = Some def) ->
                                    In w (enum q d).
Proof.
move=> d q w.
apply (enum_complete_aux d q "" w).
Qed.


(*END OF PROJECT BY CENZO POIRIER DE CARVALHO AND OSCAR PEYRON*)
