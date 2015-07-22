package body Functional_Sequences with SPARK_Mode => Off is

   function Get (S : Sequence; N : Natural) return Element_Type is
     (Element (S, N));
   function Length (S : Sequence) return Natural is
     (Natural (Length (Vector (S))));

   function Set (S : Sequence; N : Natural; E : Element_Type) return Sequence
   is
      SS : Sequence := Copy (S);
   begin
      Replace_Element (SS, N, E);
      return SS;
   end Set;

   function Empty return Sequence is
      S : Sequence;
   begin
      Clear (S);
      return S;
   end Empty;

   function Sub (S : Sequence; N1, N2 : Natural) return Sequence is
      SS : Sequence;
   begin
      for M in N1 .. N2 loop
         SS.Append (Element (S, M));
      end loop;
      return SS;
   end Sub;

   function Find (S : Sequence; E : Element_Type) return Integer is
   begin
      for I in Natural (0) ..
        Natural (Length (Element_Lists.Vector (S))) - 1 loop
         if Element (S, I) = E then
            return I;
         end if;
      end loop;
      return -1;
   end Find;

   function Snoc (S : Sequence; E : Element_Type) return Sequence
   is
      SS : Sequence := Copy (S);
   begin
      Append (SS, E);
      return SS;
   end Snoc;

end Functional_Sequences;
