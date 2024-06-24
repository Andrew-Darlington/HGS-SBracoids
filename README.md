# HGS-SBracoids
Algorithm for counting Hopf-Galois structures and skew bracoids, along with databases of results.

There are two algorithms included in this repository, represented by the files "Bracoid-HGS basic.m" and "Bracoid-HGS adv.m". They are written in the Magma programming langauge for computational algebra.

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
The file "Bracoid-HGS basic.m".
For a positive integer n, run the command:
    num_all(n);
This will produce a dataset containing two records for every group of order n. For example, "num_all(2);" gives the following output:

rec<RF1 |
    type := <2,1>,
    HGS := 1,
    Galois := 1,
    ac := 1,
    bc := 1>
rec<RF2 |
    type := <2,1>,
    sbracoids := 1,
    sbraces := 1,
    ac := 1>
In total, there are  1  HGS on separable extensions of degree  2 .  1  Galois,
and  1  a.c.  1  give bijective correspondence. There are also  1  skew bracoids
of degree  2 .  1  skew braces, and  1  a.c.

  The first record, given by the record format RF1, gives the total (denoted by "HGS") number of Hopf-Galois structures of type <n,k> on separable extensions of degree n, where <n,k> denotes the kth group of order n. It also outputs the number of those on Galois extensions, the number of those that are almost classically Galois structures ("ac"), and the number of Hopf-Galois structures which give a bijective Hopf-Galois correspondence.
  The second record, given by the record format RF2, gives the total (denoted by "sbracoids") number of skew bracoids of type <n,k> of degree n. It also outputs the number of those which are essentially skew braces ("sbraces"), and the number of bracoids which are almost classically Galois ("ac").
  The text at the end gives a summary of the above information, giving the total number of each count.

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
The file "Bracoid-HGS adv.m"
For a positive integer n, run the command:
  trans_equiv(n);
This produces a series of records containing several pieces of data regarding the number of structures (Hopf-Galois structures and skew bracoids) of each type N (group of order n) with group G (permutation group of degree n). For example, "trans_equiv(2);" gives the following output:

[
    rec<recformat<equiv_rep, class_size: IntegerRing(), isom, perm_isom,
    soluble_group, lengths, type, soluble_types, HGS_GN, sbracoid_GN> |
        equiv_rep := Symmetric group acting on a set of cardinality 2
        Order = 2
            (1, 2),
        class_size := 1,
        isom := <2, 1>,
        perm_isom := 1,
        soluble_group := true,
        lengths := [ 1 ],
        type := [ <2,1> ],
        soluble_types := [ true ],
        HGS_GN := [ [*
            rec<recformat<tot, gal, ac, bc> |
                tot := 1,
                gal := 1,
                ac := 1,
                bc := 1>,
            <2,1>
        *] ],
        sbracoid_GN := [ [*
            rec<recformat<tot, sbrace, ac> |
                tot := 1,
                sbrace := 1,
                ac := 1>,
            <2,1>
        *] ]>
]

The data can be interpreted as follows:
- "equiv_rep" gives an explicit permutation representative of the equivalence class of transitive subgroups isomorphic to G (the equivalence is isomorphism of - permutation groups).
- "class_size" gives the total number of permutation groups in the equivalence class of G.
- "isom" identifies the abstract isomorphism type of G; this may sometimes be "unknown" as G is too big and Magma cannot identify it.
- "perm_isom" identifies G in its database of transitive permutation groups (also may be "unknown" if G is not in this database).
- "soluble_group" identifies whether G is soluble or not
- For each abstract group N_i of order n, let L_i be the list of transitive subgroups M<Hol(N_i) up to conjugacy. Then "lengths" lists the sizes of each conjugacy class in each L_i. So the sum of all of these numbers should be the same as "class_size".
- For each entry in "lengths", "types" has an entry which identifies the corresponding N_i.
- "soluble_types" identifies whether each group in "types" is soluble or not.
- "HGS_GN" is a list of records, where each record gives the number of Hopf-Galois structures, with group G, admitted by each type. The fields of each record are:
    'tot', which gives the total number of such Hopf-Galois structures,
    'gal', which gives the total number of such Hopf-Galois structures when |G|=|N|, and is 0 otherwise,
    'ac', which gives the number of such Hopf-Galois structures which are almost classically Galois, and
    'bc', which gives the number of such Hopf-Galois structures which admit a bijective Hopf-Galois correspondence.
- "sbracoid_GN" is a list of records, where each record gives the number of skew bracoids, with G as its multiplicative group, of each type. The fields of each record are:
    'tot', which gives the total number of such skew bracoids,
    'sbrace', which gives the total number of such skew bracoids when |G|=|N|, and is 0 otherwise, and
    'ac', which gives the number of skew bracoids which are almost classically Galois.
--------------------------------------------------------------------------------------------------------------------------------------------------------------------
It is also important to be able to identify the group N as a subgroup of Hol(N). In Magma, this can be done as follows:
hol,f:=Holomorph(N);
SubgroupIsomorphicToN := sub<hol | [ f(g) : g in Generators(N)]>;
This is key for seeing how the groups N and G interact with each other. This has not yet been implemented in "Bracoid-HGS adv.m", but it will be included very soon!
