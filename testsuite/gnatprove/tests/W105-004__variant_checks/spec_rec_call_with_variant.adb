with SPARK.Big_Integers; use SPARK.Big_Integers;
procedure Spec_Rec_Call_With_Variant
  with
    SPARK_Mode => On
is

   function Add (C : Natural; F : not null access function (X : Integer) return Big_Integer) return Big_Integer with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Subprogram_Variant => (Decreases => C, Decreases => Max (0, F (0))),
     Post => Add'Result = F (C) + (if C = 0 then 0 else Add (C - 1, F));

   function Add (C : Natural; F : not null access function (X : Integer) return Big_Integer) return Big_Integer is
   begin
      if C = 0 then
         return F (0);
      else
         return F (C) + Add (C - 1, F);
      end if;
   end Add;

   function Add_2 (C : Natural; F : not null access function (X : Integer) return Big_Integer) return Big_Integer with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Subprogram_Variant => (Decreases => C, Decreases => Max (0, F (0))),
     Post => Add_2'Result = F (C) + (if C = 0 then 0 else Add_2 (C - 1, F));

   function Add_2 (C : Natural; F : not null access function (X : Integer) return Big_Integer) return Big_Integer is
      function F_Wrap (X : Integer) return Big_Integer is (F (X));

      procedure Prove_Post with Ghost is
      begin
         for I in 0 .. C - 1 loop
            pragma Loop_Invariant (Add_2 (I, F_Wrap'Access) = Add_2 (I, F));
         end loop;
      end Prove_Post;
   begin
      if C = 0 then
         return F (0);
      else
         Prove_Post;
         return F (C) + Add_2 (C - 1, F_Wrap'Access);
      end if;
   end Add_2;

begin
   null;
end Spec_Rec_Call_With_Variant;
