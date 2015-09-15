package P with SPARK_Mode is

   type Int_Array is array (Integer) of Integer;

   function Is_Too_Coarse (Value : Integer) return Boolean with
     Import;

   procedure Treat_Value (Value : in out Integer) with
     Import;

   procedure Read_Record (From : Integer);

   procedure Compute (X : in out Integer) with
     Contract_Cases => ((X in 1 .. 199) => X >= X'Old,
                        (X in -199 .. -1) => X <= X'Old,
                        X >= 200 => X = 200,
                        X <= -200 => X = -200);
--       Contract_Cases => ((X in -100 .. 100) => X = X'Old * 2,
--                          (X in 0 .. 199) => X = X'Old + 1,
--                          (X in -199 .. 0) => X = X'Old - 1,
--                          X >= 200 => X = 200,
--                          others => X = -200);
end P;
