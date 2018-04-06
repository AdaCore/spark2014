package body P is
   protected body PT is

      function Sum1 (Param : Integer) return Integer is
      begin
         return Param + Protected_Data;
      end;

      function Sum2 (Param : Integer) return Integer is
      begin
         return Param + Protected_Data;
      end;

   end;
end;
