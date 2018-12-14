pragma SPARK_Mode(On);

with Ada.Characters.Handling;
use  Ada.Characters.Handling;

package Names is

   subtype Domain_Name is String
     with Dynamic_Predicate => Is_Domain_Name(Domain_Name);

   -- Returns True if the given string has the format of a DNS domain name.
   function Is_Domain_Name(Name : String) return Boolean
     with Post =>
       (if Is_Domain_Name'Result then
          (for all I in Name'Range =>
             Is_Letter(Name(I)) or Is_Digit(Name(I)) or Name(I) = '-')); --@POSTCONDITION:FAIL


   -- subtype Email_Address is String
   --   with Dynamic_Predicate => Is_Email_Address(Email_Address);
   --
   -- function is_Email_Address(Address : String) return Boolean;

end Names;
