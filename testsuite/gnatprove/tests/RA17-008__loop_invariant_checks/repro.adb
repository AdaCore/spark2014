procedure Repro with SPARK_Mode is
   subtype Size_T is Natural range 0 .. 5;

   Word_Size    : constant := 32;
   Memory_Size  : constant := 2 ** Word_Size;
   type Address_Type_Base is mod Memory_Size;
   type Address_Type is new Address_Type_Base;

   type Area is record
      From, To : Address_Type;
   end record;

   Full_Area : constant Area := Area'(From => Address_Type'First,
                                      To   => Address_Type'Last);

   type Area_Array is array (Size_T range <>) of Area;

   type Ensemble (Size : Size_T) is record
      Areas : Area_Array (1 .. Size);
   end record;

   procedure Local (E : Ensemble)
     with Pre => E.Size < Size_T'Last
   is
      Result_Arr : Area_Array (1 .. E.Size + 1) := (others => Full_Area);
      Result_Pos : Size_T := 0;

      --  Ghost variable to store intermediate value of Result_Arr in order to
      --  call Lemma_Partitions on two successive values of Result_Arr.
      Save_Result_Arr : Area_Array (1 .. E.Size + 1) with Ghost;

   begin
      for E_Pos in 1 .. E.Size - 1 loop
         --  Save current value of Result_Arr in ghost variable
         Save_Result_Arr := Result_Arr;

         --  Add the following range to Result_Arr

         Result_Pos := Result_Pos + 1;
         Result_Arr(Result_Pos) :=
           Area'(From => E.Areas(E_Pos).To + 1, To => E.Areas(E_Pos + 1).From - 1);

         -- pragma Loop_Invariant (Result_Pos >= 1);  --  should not be needed ideally
         pragma Loop_Invariant (Result_Pos <= E_Pos + 1);
         pragma Loop_Invariant (Result_Arr(Result_Pos).To = E.Areas(E_Pos + 1).From - 1);
      end loop;
   end Local;
begin
   null;
end Repro;
