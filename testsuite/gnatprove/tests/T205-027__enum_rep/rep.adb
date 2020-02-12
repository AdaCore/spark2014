procedure Rep (Low : Integer; High : Integer) is
   subtype S is Integer range Low .. High;

   Y : constant Boolean :=
     S'Enum_Rep (S'First) = S'Enum_Rep (S'Last);

begin
   null;
end;
