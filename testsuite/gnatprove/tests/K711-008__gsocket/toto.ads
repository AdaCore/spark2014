package Toto is

   type Family_Type is (Family_Inet);
   type Inet_Addr_Type (Family : Family_Type := Family_Inet) is private;


   type Sock_Addr_Type (Family : Family_Type := Family_Inet) is record
      Addr : Inet_Addr_Type (Family);
   end record;

private

   type Inet_Addr_Type (Family : Family_Type := Family_Inet) is record
      case Family is
         when Family_Inet =>
            null;
      end case;
   end record;

end Toto;
