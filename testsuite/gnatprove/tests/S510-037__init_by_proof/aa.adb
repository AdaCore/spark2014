package body AA
  with SPARK_Mode
is

   procedure initGlobalsAA(Status : out Natural) is
   begin
      --
      -- make status = 0 = good for now
      -- in the "real code" we could fail and need to return error
      -- This is the point in my proposal 2) that I do NOT like
      -- would just cause and exception or similar.
      --
      Status    := 0;
      Global_AA := 1;
   end initGlobalsAA;

   procedure UseAA (X : in out Natural) is
   begin
      -- X := X + Global_Var;
      if X < Natural'Last - Global_AA then
         X := X + Global_AA;
      else
         X := 0;
      end if;
   end UseAA;

end AA;
