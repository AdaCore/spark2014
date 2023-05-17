with Cont; use Cont;
with Neverending_Loop;
with SPARK.Containers.Formal.Unbounded_Vectors;
with Ada.Unchecked_Conversion;

package body Soundness_Tests with SPARK_Mode is

   package My_Vect is new SPARK.Containers.Formal.Unbounded_Vectors
     (Index_Type    => Positive,
      Element_Type  => Integer);
   type Vector is new My_Vect.Vector;
   use all type Vector;

   type R is record
      V : Vector;
   end record;

   type Vect_Acc is access Vector;

   type Arr is array (Positive range <>) of Vector;

   subtype My_Vector is Vector;

   function Conv is new Ada.Unchecked_Conversion (My_Vector, Vector);

   procedure Selected_Component is
      V : Vector := Empty_Vector;
      Rec : R := (V => V);
   begin
      Append (Rec.V, 1);

      for I in Rec.V loop  --@TERMINATION:CHECK
         Append (Rec.V, I);
      end loop;

      for I in Rec.V loop  --@TERMINATION:CHECK
         declare
            Copy : Vector := V;
         begin
            Append (Copy, I);
            Rec := R'(V => Copy);
         end;
      end loop;
   end Selected_Component;

   procedure Identifier_Expanded_Name is
      V : Vector := Empty_Vector;
   begin
      Append (V, 1);

      for I in V loop  --@TERMINATION:CHECK
         Append (V, I);
      end loop;
   end Identifier_Expanded_Name;

   procedure Explicit_Dereference is
      Acc : Vect_Acc;
      V : Vector;
   begin
      Acc := new Vector'(V);

      for I in Acc.all loop  --@TERMINATION:CHECK
         Append (Acc.all, I);
      end loop;

   end Explicit_Dereference;

   procedure Indexed_Component is
      A : Arr (1 .. 2) := (others => <>);
   begin
      Append (A (1), 1);

      for I in A (1) loop  --@TERMINATION:CHECK
         Append (A (1), I);
      end loop;
   end Indexed_Component;

   procedure Slice is
      A : Arr (1 .. 2) := (others => <>);
   begin
      Append (A (1), 1);

      for I in A (1 .. 1) (1) loop  --@TERMINATION:CHECK
         Append (A (1), I);
      end loop;
   end Slice;

   procedure Type_Conversion is
      V : Vector;
   begin
      Append (V, 1);

      for I in My_Vector (V) loop  --@TERMINATION:CHECK
         Append (V, I);
      end loop;
   end Type_Conversion;

   procedure Qualified_Expression is
      V : Vector;
   begin
      Append (V, 1);

      for I in Vector'(V) loop  --@TERMINATION:CHECK
         Append (V, I);
      end loop;
   end Qualified_Expression;

   procedure Mix is
      A : Arr (1 .. 3);
   begin
      Append (A (1), 1);

      for I in My_Vector (Vector'(A (1 .. 1) (1))) loop  --@TERMINATION:CHECK
         Append (A (1), I);
      end loop;
   end Mix;

   procedure Withed_Object is
      use My_Sets;
   begin
      for I in Cont.S loop  --@TERMINATION:CHECK
         Cont.Include (1);
      end loop;
   end Withed_Object;

   procedure Callee is
   begin
     Neverending_Loop; --@TERMINATION:CHECK
   end Callee;
end Soundness_Tests;
