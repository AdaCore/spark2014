procedure Choice (X : Boolean; Y : in out Integer) with SPARK_Mode is
begin
   if X in True | False then
      Y := Y + 1;
   end if;
end Choice;
