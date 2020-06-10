with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;
procedure Test_Raise (X, Y : Integer) with SPARK_Mode is
   package Float_Conv is new Float_Conversions (Num => Float);

   function Rand (X : Integer) return Boolean with Import;

   procedure OK (X, Y : Integer) with
     Pre => (((X /= Y) or else raise Program_Error)
     and then (if X = 1 then raise Program_Error
          elsif X /= 2 then True
          else raise Program_Error))
     and (case X is
            when Integer'First .. - 3 => True,
            when - 1 => raise Program_Error,
            when 0 .. Integer'Last => True,
            when others => raise Program_Error)
   is
   begin
      pragma Assert ((((X /= Y) or else raise Program_Error)
                     and then (if X = 1 then raise Program_Error
                       elsif X /= 2 then True
                       else raise Program_Error))
                     and (case X is
                          when Integer'First .. - 3 => True,
                          when - 1                  => raise Program_Error,
                          when 0 .. Integer'Last    => True,
                          when others               => raise Program_Error));
   end OK;

   procedure KO (X, Y : Integer)  with
     Pre => True
   is
   begin
      pragma Assert ((((X /= Y) or else raise Program_Error)
                     and then (if X = 1 then raise Program_Error
                       elsif X /= 2 then True
                       else raise Program_Error))
                     and (case X is
                          when Integer'First .. - 3 => True,
                          when - 1                  => raise Program_Error,
                          when 0 .. Integer'Last    => True,
                          when others               => raise Program_Error));
   end KO;

   procedure KO2 (X, Y : Integer)  with
     Pre => True
   is
   begin
      if Rand (1) then
         pragma Assert (raise Program_Error or else (X /= Y));
      elsif Rand (2) then
         pragma Assert(X /= Y or raise Program_Error);
      elsif Rand (3) then
         pragma Assert (not ((X = Y) and then raise Program_Error));
      elsif Rand (4) then
         pragma Assert (if X /= 2 or else Boolean'(raise Program_Error) then True
                        else True);
      elsif Rand (5) then
         pragma Assert (if X = 1 then Boolean'(raise Program_Error)
                        else Y = Integer'(raise Program_Error));
      else
         pragma Assert (Y /= (X + Integer'(raise Program_Error)));
      end if;
   end KO2;

   Z : Big_Real := Float_Conv.To_Big_Real (0.0);
begin
   if Rand (1) and X = Y and X not in - 2 .. 2 then
      OK (X, Y); --@PRECONDITION:FAIL
   elsif Rand (2) and X /= Y and X in 1 .. 2 then
      OK (X, Y); --@PRECONDITION:FAIL
   elsif Rand (3) and X /= Y and X in -2 .. -1 then
      OK (X, Y); --@PRECONDITION:FAIL
   elsif Rand (4) and X /= Y and X not in - 2 .. 2 then
      OK (X, Y); --@PRECONDITION:PASS
   end if;

   pragma Assert (Float_Conv.From_Big_Real (Z) = 0.0); --  currently unprovable as From_Big_Real is not hard coded
end Test_Raise;
