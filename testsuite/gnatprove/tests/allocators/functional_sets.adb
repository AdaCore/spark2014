pragma Ada_2012;

package body Functional_Sets with SPARK_Mode => Off is
   use Element_Lists.Vectors;

   function Find_Element (S : Set; E : Element_Type) return Count_Type;
   --  Helper function.
   --  Searches for an element in the set and returns the appropriate index.

   function Find_Element (S : Set; E : Element_Type) return Count_Type is
   begin
      for I in 1 .. Length (S) loop
         if Element (S, I) = E then
            return I;
         end if;
      end loop;
      return 0;
   end Find_Element;

   function Mem (S : Set; E : Element_Type) return Boolean is
      (Find_Element (S, E) > 0);

   function Inc (S1, S2 : Set) return Boolean is
      I2 : Count_Type;
   begin
      for I1 in 1 .. Length (S1) loop
         I2 := Find_Element (S2, Element (S1, I1));
         if I2 = 0 then
            return False;
         end if;
      end loop;
      return True;
   end Inc;

   function "=" (S1, S2 : Set) return Boolean is
   begin
      return Inc (S1, S2) and Inc (S2, S1);
   end "=";

   function Is_Empty (S : Set) return Boolean is
     (Is_Empty (Vector (S)));

   function Is_Add (S : Set; E : Element_Type; Result : Set) return Boolean
   is
     (Mem (Result, E)
      and (for all F of Result => Mem (S, F) or F = E)
      and (for all E of S => Mem (Result, E)));

   function Add (S : Set; E : Element_Type) return Set is
   begin
      return SS : Set do
         Assign (SS, S);
         Append (SS, E);
      end return;
   end Add;

   function Remove (S : Set; E : Element_Type) return Set is
   begin
      return SS : Set do
         Assign (SS, S);
         Delete (SS, Find_Element (SS, E));
      end return;
   end Remove;

   function Is_Intersection (S1, S2, Result : Set) return Boolean is
     ((for all E of Result =>
            Mem (S1, E) and Mem (S2, E))
      and (for all E of S1 =>
               (if Mem (S2, E) then Mem (Result, E))));
   function Intersection (S1, S2 : Set) return Set is
   begin
      return SS : Set do
         for I in 1 .. Length (S1) loop
            if Find_Element (S2, Element (S1, I)) > 0 then
               Append (SS, Element (S1, I));
            end if;
         end loop;
      end return;
   end Intersection;

   function Is_Union (S1, S2, Result : Set) return Boolean is
     ((for all E of Result => Mem (S1, E) or Mem (S2, E))
      and (for all E of S1 => Mem (Result, E))
      and (for all E of S2 => Mem (Result, E)));

   function Union (S1, S2 : Set) return Set is
   begin
      return SS : Set do
         Assign (SS, S1);
         for I in 1 .. Length (S2) loop
            declare
               E : Element_Type renames Element (S2, I);
            begin
               if Find_Element (SS, E) = 0 then
                  Append (SS, Element (S2, I));
               end if;
            end;
         end loop;
      end return;
   end Union;

   function Iter_First (S : Set) return Private_Key is (First (S));
   function Iter_Has_Element (S : Set; K : Private_Key) return Boolean is
     (Has_Element (S, K));
   function Iter_Next (S : Set; K : Private_Key) return Private_Key is
     (Next (S, K));
   function Iter_Element (S : Set; K : Private_Key) return Element_Type is
     (Element (S, K));
end Functional_Sets;
