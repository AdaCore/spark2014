pragma Ada_2022;
with SPARK.Containers.Formal.Doubly_Linked_Lists;

--  Test support for the 'Loop_Index attribute for proof

procedure Test with SPARK_Mode is
   package My_List is new SPARK.Containers.Formal.Doubly_Linked_Lists
     (Integer); use My_List.Formal_Model;

   type Int_Array is array (Positive range <>) of Integer;

   --  Example with forward iteration with iterable

   function "<=" (L : My_List.List; I : Integer) return Boolean with
     Post => "<="'Result =
       (for all E of L => E <= I);

   function "<=" (L : My_List.List; I : Integer) return Boolean is
   begin
      for E of L loop
         if E > I then
            return False;
         end if;
         pragma Loop_Invariant
           (for all K in 1 .. P.Get (Positions (L), E'Loop_Index) =>
              M.Get (Model (L), K) <= I);
      end loop;
      return True;
   end "<=";

   --  Example with reverse iteration with iterable

   function "<=" (I : Integer; L : My_List.List) return Boolean with
     Post => "<="'Result =
       (for all E of L => I <= E);

   function "<=" (I : Integer; L : My_List.List) return Boolean is
   begin
      for E of reverse L loop
         if E < I then
            return False;
         end if;
         pragma Loop_Invariant
           (for all K in P.Get (Positions (L), E'Loop_Index) .. My_List.Length (L) =>
              I <= M.Get (Model (L), K));
      end loop;
      return True;
   end "<=";

   --  Example with forward iteration with array

   function "<=" (A : Int_Array; I : Integer) return Boolean with
     Post => "<="'Result =
       (for all E of A => E <= I);

   function "<=" (A : Int_Array; I : Integer) return Boolean is
   begin
      for E of A loop
         if E > I then
            return False;
         end if;
         pragma Loop_Invariant
           (for all K in A'First .. E'Loop_Index =>
              A (K) <= I);
      end loop;
      return True;
   end "<=";

   --  Example with reverse iteration with array

   function "<=" (I : Integer; A : Int_Array) return Boolean with
     Post => "<="'Result =
       (for all E of A => I <= E);

   function "<=" (I : Integer; A : Int_Array) return Boolean is
   begin
      for E of reverse A loop
         if E < I then
            return False;
         end if;
         pragma Loop_Invariant
           (for all K in E'Loop_Index .. A'Last =>
              I <= A (K));
      end loop;
      return True;
   end "<=";
begin
   null;
end;
