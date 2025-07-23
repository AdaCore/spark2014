package body My_Integer_Sets with SPARK_Mode is
   use all type Inst.Formal_Model.M.Set;

   function Model (X : Set) return Set_Models.Set with
     Refined_Post =>
       Length (Model'Result) = Length (Inst.Formal_Model.Model (X.Impl))
       and then
         (for all I in My_Int =>
            Contains (Model'Result, I) = Contains (Inst.Formal_Model.Model (X.Impl), I))
   is
      use all type Inst.Formal_Model.P.Map;
      use all type Inst.Formal_Model.E.Sequence;
      use all type Set_Models.Set;
   begin
      return Res : Set_Models.Set do
         for C in X.Impl loop
            Res := Add (Res, Inst.Element (X.Impl, C));
            pragma Loop_Invariant
              (Length (Res) = Inst.Formal_Model.E.Big
	        (Get (Inst.Formal_Model.Positions (X.Impl), C)));
            pragma Loop_Invariant
              (for all I in My_Int =>
                 Contains (Res, I) =
               (for some J in 1 .. Get (Inst.Formal_Model.Positions (X.Impl), C) =>
                        I = Get (Inst.Formal_Model.Elements (X.Impl), J)));
         end loop;
         Inst.Formal_Model.Lift_Abstraction_Level (X.Impl);
      end return;
   end Model;

   function Cardinality (X : Set) return Natural is
   begin
      return Natural (Inst.Length (X.Impl));
   end Cardinality;

   function Contains (X : Set; Y : My_Int) return Boolean is
   begin
      return Inst.Contains (X.Impl, Y);
   end Contains;

   procedure Add (X : in out Set; Y : My_Int) is
      procedure Lemma_Capacity_Is_Enough (X : Inst.Set; Y : My_Int) with
        Ghost,
        Post => (if not Inst.Contains (X, Y) then Inst.Length (X) < 201);
      --  Prove that there is enough room to add a new element in the set

      procedure Lemma_Capacity_Is_Enough (X : Inst.Set; Y : My_Int) is
         Z : Inst.Formal_Model.M.Set;
      begin
         for I in My_Int'Range loop
            if Inst.Contains (X, I) then
               Z := Add (Z, I);
            end if;
            pragma Loop_Invariant
	      (Length (Z) <= To_Big_Integer (Integer (I) -
	         Integer (My_Int'First) + 1));
            pragma Loop_Invariant
	      ((Length (Z) = To_Big_Integer (Integer (I) -
	         Integer (My_Int'First) + 1)) =
	       (for all K in My_Int'First .. I => Inst.Contains (X, K)));
            pragma Loop_Invariant (Z <= Inst.Formal_Model.Model (X));
            pragma Loop_Invariant (for all K of Z => K <= I);
            pragma Loop_Invariant (for all K of X => Contains (Z, K) or K > I);
         end loop;
         pragma Assert (Num_Overlaps (Z, Inst.Formal_Model.Model (X)) = Length (Z));
      end Lemma_Capacity_Is_Enough;
   begin
      Lemma_Capacity_Is_Enough (X.Impl, Y);
      Inst.Include (X.Impl, Y);
   end Add;
end;
