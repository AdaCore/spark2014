   procedure Silly (X      : in  Positive;
                    Y      : in  Positive;
                    Result : out Positive)
      with
         SPARK_Mode,
         Pre => ((X + Y) / 2 in Positive)
   is
   begin
      if X > 10 then
         Result := 1;
      else
         Result := Y / 2 + 1;
      end if;
   end Silly;
