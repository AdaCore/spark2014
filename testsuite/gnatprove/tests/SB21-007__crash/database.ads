with Email; use Email;
with Ada.Containers.Functional_Sets;

--  Interface to the database. It can be implemented using local datastructures
--  (like here) or a persistent mechanism (file system, sql database...).

package Database with SPARK_Mode,
  Initial_Condition => Invariant
  is

   --  The model of a database is a set of pairs of a key and an email

   type DB_Entry_Type is record
      Key   : Integer;
      Email : Email_Address_Type;
   end record;

   package DB_Entry_Sets is new Ada.Containers.Functional_Sets
     (Element_Type => DB_Entry_Type);
   use DB_Entry_Sets;
   subtype Model_Type is DB_Entry_Sets.Set with Ghost;

   --  Invariant linking the model of our database to its content

   function Invariant return Boolean with
     Ghost;

end Database;
