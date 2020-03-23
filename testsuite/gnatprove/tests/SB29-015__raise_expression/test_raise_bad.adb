procedure Test_Raise_Bad (X, Y : Integer) with SPARK_Mode is

   procedure Bad (X, Y : Integer) with
     Import,
     Pre => ((raise Program_Error or else (X /= Y))
     and then (((X /= Y) or raise Program_Error)
     and then not ((X = Y) and then raise Program_Error)
     and then (if X = 1 then Boolean'(raise Program_Error)
          elsif X /= 2 or else Boolean'(raise Program_Error) then True
          else Y = (raise Program_Error))))
       and then Y /= (X + (raise Program_Error));
begin
   null;
end Test_Raise_Bad;
