theory Multl_Pattern_Matching
  imports HashTrie HashTrie_TM
begin
(*---------------------------Multi-pattern matching based on HashTrie---------------------------*)
primrec hashtrie_automata::"('a list * 'v) list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a,'v) hashtrie"
  where"hashtrie_automata [] t = t"|
       "hashtrie_automata (x#xs) t = hashtrie_automata xs (insert_hashtrie (fst x) (snd x) t)"

primrec hashtrie_match::"'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> 'v list"
  where"hashtrie_match [] t vs = vs"|
       "hashtrie_match (x#xs) t vs = (case text_in_hashtrie t (x#xs) of None \<Rightarrow> hashtrie_match xs t vs|
                                                                    Some b \<Rightarrow> hashtrie_match xs t (vs@[b]))"

definition set_val_hashtrie :: "('a,'v) hashtrie \<Rightarrow> 'v set" where
[simp]: "set_val_hashtrie t = {v. (\<exists>xs. xs \<in> set_hashtrie t \<and> lookup_hashtrie t xs = Some v)}"

lemma l2:"\<And>t. text_in_hashtrie t l = Some v \<Longrightarrow> \<exists>as bs. l = as @ bs \<longrightarrow> lookup_hashtrie t as = Some v"
  apply(induct l)
   apply auto
  done

lemma text_in_hashtrie: "text_in_hashtrie t l = Some v \<Longrightarrow> \<exists>xs. isin_hashtrie xs t \<and> lookup_hashtrie t xs = Some v"
  apply(induct t l rule:text_in_hashtrie.induct)
   apply (metis isin_hashtrie.simps(2) lookup_hashtrie.simps(1) text_in_hashtrie.simps(1))
  apply(auto split:option.splits)
  apply (meson isin_hashtrie.simps(2) lookup_hashtrie.simps(1))
  by (metis HashTrie.set_hashtrie_def lookup_Some_set lookup_hashtrie.simps(1)
             lookup_hashtrie.simps(2) mem_Collect_eq option.simps(5))

theorem match_in_hashtrie :"\<forall>v\<in>set (hashtrie_match l t vs). v \<in> set_val_hashtrie t \<or> v \<in> set vs"
  apply(induct l arbitrary: t vs)
   apply simp
  apply(auto split:option.splits)
  by (metis text_in_hashtrie rotate1.simps(2) set_ConsD set_rotate1)

fun text_in_hashtrie_tm::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option tm"
  where"text_in_hashtrie_tm (Nd b _ _) [] =1 return b"|
       "text_in_hashtrie_tm (Nd b kts m) (x#xs) =1
             (if b = None then (case m x of None \<Rightarrow> return None | 
                                          Some t \<Rightarrow> text_in_hashtrie_tm t xs)
                          else return b)"

definition V_text_in_hashtrie :: "('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option"
  where "V_text_in_hashtrie t xs = val(text_in_hashtrie_tm t xs)"

definition T_text_in_hashtrie :: "('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> nat"
  where "T_text_in_hashtrie t xs = time(text_in_hashtrie_tm t xs)"

lemma V_text_in_hashtrie:"V_text_in_hashtrie t xs = text_in_hashtrie t xs"
  apply(induct t xs rule:text_in_hashtrie.induct)
   by (simp add: V_text_in_hashtrie_def option.case_eq_if)+

fun hashtrie_match_tm::"'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> 'v list tm"
  where"hashtrie_match_tm [] t vs =1 return vs"|
       "hashtrie_match_tm (x#xs) t vs =1 
                   do { v \<leftarrow> text_in_hashtrie_tm t (x#xs);
                        case v of None \<Rightarrow> hashtrie_match_tm xs t vs|
                                  Some b \<Rightarrow> hashtrie_match_tm xs t (vs@[b]) }"  

definition V_hashtrie_match :: "'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> 'v list" where
"V_hashtrie_match xs t vs = val(hashtrie_match_tm xs t vs)"

definition T_hashtrie_match :: "'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> nat" where
"T_hashtrie_match xs t vs = time(hashtrie_match_tm xs t vs)"

theorem V_hashtrie_match:" V_hashtrie_match xs t vs = hashtrie_match xs t vs"
  apply(induct xs arbitrary: t vs)
   apply (simp add:V_hashtrie_match_def V_text_in_hashtrie_def)+
  by (metis V_text_in_hashtrie V_text_in_hashtrie_def option.case_distrib)

(*-----------------------------Multi-pattern matching based on Trie-----------------------------*)
primrec trie_automata::"('k list * 'v) list \<Rightarrow> ('k, 'v) trie \<Rightarrow> ('k, 'v) trie"
  where"trie_automata [] t = t"|
       "trie_automata (k#ks) t = trie_automata ks (update_trie (fst k) (snd k) t)"

fun text_in_trie::"('k,'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option"
  where"text_in_trie (Trie v kts) [] = v"|
       "text_in_trie (Trie v kts) (k#ks) = 
             (if v = None then (case map_of kts k of None \<Rightarrow> None|
                                                     Some st \<Rightarrow> text_in_trie st ks)
                          else v)"

primrec trie_match::"'k list \<Rightarrow> ('k,'v) trie \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where"trie_match [] t vs = vs"|
       "trie_match (k#ks) t vs = (case text_in_trie t (k#ks) of None \<Rightarrow> trie_match ks t vs|
                                                                    Some b \<Rightarrow> trie_match ks t (vs@[b]))"

fun text_in_trie_tm::"('k,'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option tm"
  where"text_in_trie_tm (Trie v kts) [] =1 return v"|
       "text_in_trie_tm (Trie v kts) (k#ks) =1
             (if v = None then do{ s_t \<leftarrow> map_of_tm kts k;
                                    case s_t of None \<Rightarrow> return None|
                                                Some st \<Rightarrow> text_in_trie_tm st ks}
                          else return v)"

definition V_text_in_trie :: "('k,'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option"
  where "V_text_in_trie t xs = val(text_in_trie_tm t xs)"

definition T_text_in_trie :: "('k,'v) trie \<Rightarrow> 'k list \<Rightarrow> nat"
  where "T_text_in_trie t xs = time(text_in_trie_tm t xs)"

lemma V_text_in_trie:"V_text_in_trie t xs = text_in_trie t xs"
  apply (induct t xs rule:text_in_trie.induct)
  apply (auto simp:V_text_in_trie_def)+
  by (metis V_map_of V_map_of_def option.case_eq_if option.exhaust_sel val_return)

fun trie_match_tm::"'k list \<Rightarrow>  ('k,'v) trie \<Rightarrow> 'v list  \<Rightarrow> 'v list tm"
  where"trie_match_tm [] t vs =1 return vs"|
       "trie_match_tm (x#xs) t vs =1 
                   do { v \<leftarrow> text_in_trie_tm t (x#xs);
                        case v of None \<Rightarrow> trie_match_tm xs t vs|
                                  Some b \<Rightarrow> trie_match_tm xs t (vs@[b]) }"   

definition V_trie_match :: "'k list \<Rightarrow>  ('k,'v) trie \<Rightarrow> 'v list  \<Rightarrow> 'v list" where
"V_trie_match xs t vs = val(trie_match_tm xs t vs)"

definition T_trie_match :: "'k list \<Rightarrow>  ('k,'v) trie \<Rightarrow> 'v list  \<Rightarrow> nat" where
"T_trie_match xs t vs = time(trie_match_tm xs t vs)"

theorem V_trie_match:"V_trie_match xs t vs = trie_match xs t vs"
 apply(induct xs arbitrary: t vs)
   apply (simp add:V_trie_match_def V_text_in_trie_def)+
  by (metis V_text_in_trie V_text_in_trie_def option.case_distrib)

(*---------------------------Threaded multi-pattern matching based on HashTrie---------------------------*)
fun suffix_subhashtrie::"'a list \<Rightarrow> nat \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> 'a list * ('a,'v) hashtrie"
  where"suffix_subhashtrie [] _ t = ([], empty_hashtrie)"|
       "suffix_subhashtrie (x#xs) 0 t = suffix_subhashtrie xs 1 t"|
       "suffix_subhashtrie (x#xs) n t = (case (find_subhashtrie t (x#xs)) of None \<Rightarrow> (suffix_subhashtrie xs (Suc n) t)|
                                                                     Some subt \<Rightarrow> ((x#xs), subt))"

primrec f_index::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a list * ('a,'v) hashtrie) list \<Rightarrow> ('a list * ('a,'v) hashtrie) list"
  where"f_index [] t pre f = f"|
       "f_index (x#xs) t pre f = (if length pre < 2 then f_index xs t (pre@[x]) (f@[([], empty_hashtrie)])
                                                    else f_index xs t (pre@[x]) (f@[suffix_subhashtrie pre 0 t]))"

primrec failure_index::"('a list * 'v) list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a list * ('a,'v) hashtrie) list list  \<Rightarrow> ('a list * ('a,'v) hashtrie) list list"
  where"failure_index [] t findex = findex"|
       "failure_index (x#xs) t findex = failure_index xs t (findex@[(f_index (fst x) t [] [])])"

fun s_index::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a list * ('a,'v) hashtrie) list \<Rightarrow> ('a list * ('a,'v) hashtrie) list"
  where"s_index [] t pre s = s"|
       "s_index (x#[]) t pre s = s@[suffix_subhashtrie (pre@[x]) 0 t]"|
       "s_index (x#xs) t pre s = s_index xs t (pre@[x]) s"

primrec success_index::"('a list * 'v) list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a list * ('a,'v) hashtrie) list  \<Rightarrow> ('a list * ('a,'v) hashtrie) list"
  where"success_index [] t success = success"|
       "success_index (x#xs) t success = success_index xs t (success@(s_index (fst x) t [] []))"

primrec kw_n:: "'a list \<Rightarrow>  ('a list * 'v) list \<Rightarrow> nat \<Rightarrow> nat option"
  where"kw_n p [] n = None"|
       "kw_n p (x#xs) n = (if (take (length p) (fst x)) = p then Some n else kw_n p xs (Suc n))"

fun hashtrie_threaded_m::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a list * 'v) list \<Rightarrow> ('a list * ('a,'v) hashtrie) list list \<Rightarrow>
                         ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> ('a list \<times> 'v list)"
  where "hashtrie_threaded_m (Nd None _ _) [] kw fi si mpre tpre vs = (tpre,vs)" |
        "hashtrie_threaded_m (Nd (Some v) _ _) [] kw fi si mpre tpre vs = (tpre,vs@[v])" |
        "hashtrie_threaded_m (Nd b kts m) (x#xs) kw fi si mpre tpre vs =
           (if b = None then (case m x of None \<Rightarrow> (if (length mpre)<2 \<or> (kw_n mpre kw 0) = None 
                                                   then (tpre,vs) 
                                                   else ((let n = the (kw_n mpre kw 0);
                                                              (f_mpre,f_ht) = fi!n!(length mpre - 1)
                                                           in (if f_mpre = []\<or>length f_mpre \<ge> length mpre
                                                               then (tpre,vs)
                                                               else hashtrie_threaded_m f_ht (x#xs) kw fi si f_mpre tpre vs))))| 
                                          Some t \<Rightarrow> hashtrie_threaded_m t xs kw fi si (mpre@[x]) (tpre@[x]) vs)
                        else (let n = the (kw_n mpre kw 0);
                                  (s_mpre,s_ht) = si!n
                              in (if s_mpre = []\<or>length s_mpre \<ge> length mpre
                                  then (tpre,vs@[the b])
                                  else hashtrie_threaded_m s_ht (x#xs) kw fi si s_mpre tpre (vs@[the b]))))"

fun hashtrie_threaded_m_tm::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a list * 'v) list \<Rightarrow> ('a list * ('a,'v) hashtrie) list list \<Rightarrow>
                            ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> ('a list \<times> 'v list) tm"
  where "hashtrie_threaded_m_tm (Nd None _ _) [] kw fi si mpre tpre vs =1 return (tpre,vs)" |
        "hashtrie_threaded_m_tm (Nd (Some v) _ _) [] kw fi si mpre tpre vs =1 return (tpre,vs@[v])" |
        "hashtrie_threaded_m_tm (Nd b kts m) (x#xs) kw fi si mpre tpre vs =1
           (if b = None then (case m x of None \<Rightarrow> (if (length mpre)<2 \<or> (kw_n mpre kw 0) = None 
                                                   then return (tpre,vs) 
                                                   else ((let n = the (kw_n mpre kw 0);
                                                              (f_mpre,f_ht) = fi!n!(length mpre - 1)
                                                           in (if f_mpre = []\<or>length f_mpre \<ge> length mpre
                                                               then return (tpre,vs)
                                                               else hashtrie_threaded_m_tm f_ht (x#xs) kw fi si f_mpre tpre vs))))| 
                                          Some t \<Rightarrow> hashtrie_threaded_m_tm t xs kw fi si (mpre@[x]) (tpre@[x]) vs)
                        else (let n = the (kw_n mpre kw 0);
                                  (s_mpre,s_ht) = si!n
                              in (if s_mpre = []\<or>length s_mpre \<ge> length mpre
                                  then return (tpre,vs@[the b])
                                  else hashtrie_threaded_m_tm s_ht (x#xs) kw fi si s_mpre tpre (vs@[the b]))))"

definition V_hashtrie_threaded_m :: "('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a list * 'v) list \<Rightarrow> ('a list * ('a,'v) hashtrie) list list \<Rightarrow>
                                     ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> ('a list \<times> 'v list)"
  where "V_hashtrie_threaded_m ht t kw fi si mpre tpre vs = val(hashtrie_threaded_m_tm ht t kw fi si mpre tpre vs)"

definition T_hashtrie_threaded_m :: "('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a list * 'v) list \<Rightarrow> ('a list * ('a,'v) hashtrie) list list \<Rightarrow>
                                     ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'v list \<Rightarrow> nat"
  where "T_hashtrie_threaded_m ht t kw fi si mpre tpre vs = time(hashtrie_threaded_m_tm ht t kw fi si mpre tpre vs)"



fun hashtrie_threaded_match::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a list * 'v) list  \<Rightarrow> ('a list * ('a,'v) hashtrie) list list
                                \<Rightarrow> ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where"hashtrie_threaded_match [] ht kw fi si vs = vs"|
       "hashtrie_threaded_match (x#xs) ht kw fi si vs = (let (tpre,vs') = hashtrie_threaded_m ht (x#xs) kw fi si [] [] vs
                                                         in (if tpre = []
                                                             then hashtrie_threaded_match xs ht kw fi si vs'
                                                             else hashtrie_threaded_match (drop (length tpre) (x#xs)) ht kw fi si vs'))"

fun hashtrie_threaded_match_tm::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a list * 'v) list  \<Rightarrow> ('a list * ('a,'v) hashtrie) list list
                                  \<Rightarrow> ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'v list \<Rightarrow> 'v list tm"
  where"hashtrie_threaded_match_tm [] ht kw fi si vs =1 return vs"|
       "hashtrie_threaded_match_tm (x#xs) ht kw fi si vs =1 
                                          do { one \<leftarrow> hashtrie_threaded_m_tm ht (x#xs) kw fi si [] [] vs;
                                               let (tpre,vs') = one
                                               in (if tpre = []
                                                   then hashtrie_threaded_match_tm xs ht kw fi si vs'
                                                   else hashtrie_threaded_match_tm (drop (length tpre) (x#xs)) ht kw fi si vs')}"


definition V_hashtrie_threaded_match::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a list * 'v) list  \<Rightarrow> ('a list * ('a,'v) hashtrie) list list
                                        \<Rightarrow> ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where"V_hashtrie_threaded_match t ht kw fi si vs = val (hashtrie_threaded_match_tm t ht kw fi si vs)"

definition T_hashtrie_threaded_match::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a list * 'v) list  \<Rightarrow> ('a list * ('a,'v) hashtrie) list list
                                        \<Rightarrow> ('a list * ('a,'v) hashtrie) list \<Rightarrow> 'v list \<Rightarrow> nat"
  where"T_hashtrie_threaded_match t ht kw fi si vs = time (hashtrie_threaded_match_tm t ht kw fi si vs)"

lemma V_hashtrie_threaded_m:"V_hashtrie_threaded_m ht t kw fi si mpre tpre vs 
                             = hashtrie_threaded_m ht t kw fi si mpre tpre vs"
  apply (induct rule:hashtrie_threaded_m.induct)
  by (auto simp:V_hashtrie_threaded_m_def option.case_eq_if split:prod.splits)+

theorem V_hashtrie_threaded_match:"V_hashtrie_threaded_match t ht kw fi si vs 
                                   = hashtrie_threaded_match t ht kw fi si vs"
  apply (induct t ht kw fi si vs rule:hashtrie_threaded_match.induct)
  apply (auto simp:V_hashtrie_threaded_match_def option.case_eq_if split:prod.splits)
  by (metis V_hashtrie_threaded_m V_hashtrie_threaded_m_def prod.inject)+


end
