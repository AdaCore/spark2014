procedure Test is
   type Discriminated_Record (Discriminant : Boolean := False) is record
      case Discriminant is
         when True =>
            Component : Integer;
         when False =>
            null;
      end case;
   end record;

   type Enclosing_Record is record
      DR : Discriminated_Record;
   end record;

   -- this assignment triggers a crash
   ER : Enclosing_Record := (others => <>);
begin
   null;
end Test;
