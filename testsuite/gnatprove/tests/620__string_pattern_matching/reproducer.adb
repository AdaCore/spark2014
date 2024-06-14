 function Reproducer
   (URI : String) return Boolean
 with SPARK_Mode => On
is
 begin
    case URI is
       when "demo" =>
          return True;
       when others =>
          return False;
    end case;
      return False;
 end Reproducer;
