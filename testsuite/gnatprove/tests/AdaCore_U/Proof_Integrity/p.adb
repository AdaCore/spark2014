package body P with SPARK_Mode is
   Memory : Int_Array;
   Size, Data1, Data2, Addr : Integer;

   procedure Read_Record (From : Integer)
   is
      function ReadOne (First : Integer; Offset : Integer)
                     return Integer --  with
      -- Pre => Memory'Last - Offset >= Memory (First)
      -- Pre => Memory (First) + Offset in Memory'Range
      is
         Value : Integer := Memory (Memory (First) + Offset);
      begin
         if Is_Too_Coarse (Value) then
            Treat_Value (Value);
         end if;
         return Value;
      end ReadOne;
   begin
      Size := ReadOne (From, 0);
      pragma Assume (Size in 1 .. 10
                     and then Memory (From) < Integer'Last - 2 * Size);
      Data1 := ReadOne (From, 1);
      Addr  := ReadOne (From, Size + 1);
      pragma Assume (Memory (Addr) > Memory (From) + Size);
      Data2 := ReadOne (Addr, -Size);
   end Read_Record;

   procedure Compute (X : in out Integer) is
   begin
      if X in -100 .. 100 then
         X := X * 2;
      elsif X in 0 .. 199 then
         X := X + 1;
      elsif X in -199 .. 0 then
         X := X - 1;
      elsif X >= 200 then
         X := 200;
      else
         X := -200;
      end if;
   end Compute;
end P;
