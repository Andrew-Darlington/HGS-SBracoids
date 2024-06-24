//returns |Aut(G,G')| along with the list of images of G' under automorphisms of G 	
NumOfAutomorphisms:=function(G);
	A:=AutomorphismGroup(G);
	ng:=Ngens(A);
	prep,P:=PermutationRepresentation(A);
	//generators of A should correspond to those of P --> we check it:
	assert ng eq Ngens(P) and forall{i: i in [1..ng] | A.i @ prep eq P.i};

	//Computation of automorphisms of G sending Stab(G,1) to itself
	Gprime:=[Stabiliser(G,1)]; //images of Stab(G,1) under automorphisms
	perms:=[[]: i in [1..ng]];  //permutations of Gprime induced by A.i
	j:=1;
	while j le #Gprime do
		S:=Gprime[j];
		for i in [1..ng] do
			im:=(A.i)(S);
			pos:=Position(Gprime,im);
			if pos eq 0 then //new image
				Append(~Gprime,im);
				pos:=#Gprime;
			end if;
			Append(~perms[i],pos);
		end for;
		j:=j+1;
	end while;
	pgp:=sub<Sym(#Gprime) | {Sym(#Gprime)!perms[i]: i in [1..ng]}>;
	act:=hom<P->pgp | perms>;
	Q:=Stabiliser(pgp,1) @@ act;
	return [*#Q,Gprime*];
end function;

//given an equivalence class of transitive permutation groups, returns the number of HGS of each type
NG := function(n,trans_types,trans_lengths,G_a,Reg,AC,BC);
	RF1:=recformat<tot,gal,ac,bc>;
	RF2:=recformat<tot,sbrace,ac>;
	HGS_sbracoid_list:=[];
	mul_type:=SequenceToMultiset(trans_types);		//types with multiplicities
	T:=IndexedSet(trans_types);						
	T:=IndexedSetToSequence(T);						//ordered list of types associated to x
	freq_type:=[Multiplicity(mul_type,c) : c in T];	//ordered list of multiplicities
	M:=[0];					//sequence of cumulative sums of the multiplicities in freq_type
	j:=0;
	for i in freq_type do
		j:=j+i;
		Append(~M,j);
	end for;	
	a:=2;
	for i in M do				//obtains the explicit number of equivalent permutation groups with each type
		if not i eq M[#M] then
			b:=i+1;
			hgs1:=0;
			hgs2:=0;
			hgs3:=0;
			hgs4:=0;
			sb1:=0;
			sb2:=0;
			sb3:=0;
			for j in [b..M[a]] do
				hgs1:=hgs1+trans_lengths[j];
				sb1:=sb1+1;
				if Reg[j] eq "yes" then
					hgs2:=hgs2+trans_lengths[j];
					sb2:=sb2+1;
				end if;
				if BC[j] eq "yes" then
					hgs3:=hgs3+trans_lengths[j];
					if AC[j] eq "yes" then
						hgs4:=hgs4+trans_lengths[j];
						sb3:=sb3+1;
					end if;
				end if;
			end for;
			Append(~HGS_sbracoid_list,[*hgs1,hgs2,hgs3,hgs4,sb1,sb2,sb3,T[a-1],Order(AutomorphismGroup(SmallGroups(n)[StringToInteger(Substring(T[a-1],#IntegerToString(n)+3,#T[a-1]-(#IntegerToString(n)+3)))]))*]);
			a:=a+1;
		end if;
	end for;
	numHGS:=[];
	numSbracoids:=[];
	for u in HGS_sbracoid_list do
		autgh:=(G_a/u[9]);
		r1:=rec<RF1 | tot:=autgh*u[1],gal:=autgh*u[2],bc:=autgh*u[3],ac:=autgh*u[4]>;
		Append(~numHGS,[*r1,u[8]*]);
		r2:=rec<RF2 | tot:=u[5],sbrace:=u[6],ac:=u[7]>;
		Append(~numSbracoids,[*r2,u[8]*]);
	end for;
	return [*numHGS,numSbracoids*];
end function;

//given an integer n, outputs a list of all (Hol(N) for each N) transitive subgroups with other data
data:=function(n);
	stabs:=[];
	types:=[];
	sol_types:=[];
	G_autord:=[];
	trans:=[];
	length:=[];
	isReg:=[];
	isAC:=[];
	isBC:=[];
	i:=1;
	for A in SmallGroups(n) do
		N_soluble:=IsSolvable(A);
		hol,f:=Holomorph(A);
		SubgroupIsomorphicToA := sub<hol | [ f(g) : g in Generators(A)]>;
		t := Subgroups(hol:OrderMultipleOf := n, IsTransitive:=true);
		for G in t do
			intfields:=#IntermediateSubgroups(G`subgroup,Stabiliser(G`subgroup,1))+2;
			subGst:=0;
			for N in AllSubgroups(SubgroupIsomorphicToA) do
				if G`subgroup subset Normalizer(hol,N) then
					subGst:=subGst+1;
				end if;
			end for;
			if G`order eq n then
				Append(~stabs,[PermutationGroup<{1..n} | [] >]);
				Append(~G_autord,Order(AutomorphismGroup(G`subgroup)));
				Append(~trans,G`subgroup);
				Append(~length,G`length);
				Append(~isReg,"yes");
				if Centralizer(SymmetricGroup(n),SubgroupIsomorphicToA) subset G`subgroup then
					Append(~isAC,"yes");
				else
					Append(~isAC,"no");
				end if;
				if intfields eq subGst then
					Append(~isBC,"yes");
				else
					Append(~isBC,"no");
				end if;
			else
				NumAut:=NumOfAutomorphisms(G`subgroup);
				Append(~stabs,NumAut[2]);
				Append(~G_autord,NumAut[1]);
				Append(~trans,G`subgroup);
				Append(~length,G`length);
				Append(~isReg,"no");
				if Centralizer(SymmetricGroup(n),SubgroupIsomorphicToA) subset G`subgroup then
					Append(~isAC,"yes");
				else
					Append(~isAC,"no");
				end if;
				if intfields eq subGst then
					Append(~isBC,"yes");
				else
					Append(~isBC,"no");
				end if;
			end if;
		end for;
		types:=types cat ["<" cat IntegerToString(n) cat "," cat IntegerToString(i) cat ">" : j in [1..#t]];
		sol_types:=sol_types cat [N_soluble : j in [1..#t]];
		i:=i+1;
	end for;
	RF:=recformat<transitive_groups,lengths,autGGprime_ord,autGGprime_im,Ntypes,Ntypes_sol,reg,ac,bc>;
	r:=rec<RF | transitive_groups:=trans,lengths:=length,autGGprime_ord:=G_autord,autGGprime_im:=stabs,Ntypes:=types,Ntypes_sol:=sol_types,reg:=isReg,ac:=isAC,bc:=isBC>;
	return r;
end function;
	


//this function sorts the transitive subgroups into isomorphism classes
trans_equiv := function(n);
	classes:=[];	//list of equivalence classes
	used_groups:=[]; //groups which have already been sorted into equivalence classes
	d:=data(n);
	k:=1;
	for x in d`transitive_groups do
		if Index(used_groups,k) eq 0 then
			try
				id:=IdentifyGroup(x);
			catch e;
				id:="unknown";
			end try;
			try
				perm_id:=TransitiveGroupIdentification(x);
			catch e;
				perm_id:="unknown";
			end try;
			G_soluble:=IsSolvable(x);
			trans_lengths:=[];
			trans_types:=[];
			trans_soltypes:=[];
			isReg:=[];
			isAC:=[];
			isBC:=[];
			i:=k;
			s:=0;
			for y in [d`transitive_groups[j] : j in [k..#(d`transitive_groups)]] do //only need to run from x up to end
				if Index(used_groups,i) eq 0 then
					bool,isom:=IsIsomorphic(x,y);
					if bool eq true then
						if Position(d`autGGprime_im[i],isom(Stabiliser(x,1))) gt 0 then
							Append(~trans_lengths,d`lengths[i]);
							Append(~trans_types,d`Ntypes[i]);
							Append(~trans_soltypes,d`Ntypes_sol[i]);
							Append(~isReg,d`reg[i]);
							Append(~isAC,d`ac[i]);
							Append(~isBC,d`bc[i]);
							Append(~used_groups,i);
							s:=s+d`lengths[i];
						end if;
					end if;
				end if;
				i:=i+1;
			end for;
			if #trans_lengths gt 0 then
				nums:=NG(n,trans_types,trans_lengths,d`autGGprime_ord[k],isReg,isAC,isBC);
				RF:=recformat<equiv_rep, class_size : Integers(),isom, perm_isom, soluble_group, lengths, type, soluble_types, HGS_GN,sbracoid_GN>;
				r:=rec<RF | equiv_rep:=x, class_size:=s,isom:=id, perm_isom:=perm_id, soluble_group:=G_soluble, lengths:=trans_lengths, type:=trans_types, soluble_types:=trans_soltypes, HGS_GN:=nums[1],sbracoid_GN:=nums[2]>;
				Append(~classes,r);
			end if;
		end if;
		k:=k+1;
	end for;
	return classes; //list of equivalence classes along with size of each one
end function;