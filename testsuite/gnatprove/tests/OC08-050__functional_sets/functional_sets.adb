pragma Ada_2012;

package body Functional_Sets with SPARK_Mode => Off is
   use Element_Lists;

   function Mem (S : Set; E : Element_Type) return Boolean is
      (Contains (S, E));

   function Inc (S1, S2 : Set) return Boolean is
      I2 : Extended_Index;
   begin
      for I1 in 1 .. Natural (Length (S1)) loop
         I2 := Find_Index (S2, Element (S1, I1));
         if I2 = No_Index then
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
      and (for all F in Result => Mem (S, F) or F = E)
      and (for all E in S => Mem (Result, E)));

   function Add (S : Set; E : Element_Type) return Set is
      SS : Set := Copy (S);
   begin
      Append (SS, E);
      return SS;
   end Add;


   function Is_Intersection (S1, S2, Result : Set) return Boolean is
     ((for all E in Result =>
            Mem (S1, E) and Mem (S2, E))
      and (for all E in S1 =>
               (if Mem (S2, E) then Mem (Result, E))));
   function Intersection (S1, S2 : Set) return Set is
      Cu : Cursor := First (S1);
      SS : Set;
   begin
      while Has_Element (Cu) loop
         if Contains (S2, Element (Cu)) then
            Append (SS, Element (Cu));
         end if;
         Next (Cu);
      end loop;
      return SS;
   end Intersection;

   function Is_Union (S1, S2, Result : Set) return Boolean is
     ((for all E in Result => Mem (S1, E) or Mem (S2, E))
      and (for all E in S1 => Mem (Result, E))
      and (for all E in S2 => Mem (Result, E)));

   function Union (S1, S2 : Set) return Set is
      SS : Set := Copy (S1);
   begin
      Append (SS, S2);
      return SS;
   end Union;

   function First_Element (S : Set) return Element_Type is
      (if Is_Empty (Vector (S)) then No_Element else Element (S, 1));
   function Next_Element (S : Set; E : Element_Type) return Element_Type is
     (if Find_Index (S, E) in 1 .. Natural (Length (S)) - 1
      then Element (S, Find_Index (S, E) + 1)
      else No_Element);
end Functional_Sets;
