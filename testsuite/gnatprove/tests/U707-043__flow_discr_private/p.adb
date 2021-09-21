with Super; use Super;

package body P with SPARK_Mode is
      function Id
        (Source : Typ) return Typ
      is
      begin
         return Result : Typ do
            Result := Super_Id (Source);
         end return;
      end Id;
end P;
