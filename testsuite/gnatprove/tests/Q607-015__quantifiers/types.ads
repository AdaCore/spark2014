package Types with SPARK_Mode is
  type T_Arr is array (Positive range <>) of Integer;

--     type Option (Exists : Boolean) is record
--        case Exists is
--           when True => Value : Integer;
--           when False => null;
--        end case;
--     end record;

   type Option is record
      Exists : Boolean;
      Value : Integer;
   end record;
end Types;
