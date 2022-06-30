with SPARK.Containers.Formal.Doubly_Linked_Lists;

package body Database with SPARK_Mode is

   type DB_Entry_Type is record
      Key : Integer;
      Email : Email_Access;
   end record;

   function "=" (X, Y : DB_Entry_Type) return Boolean is
     (X.Key = Y.Key
      and then (X.Email = null) = (Y.Email = null)
      and then (if X.Email /= null then X.Email.all = Y.Email.all));

   package DB_Pack is new SPARK.Containers.Formal.Doubly_Linked_Lists
     (Element_Type => DB_Entry_Type,
      "="          => "=");

   Database : DB_Pack.List (1000);

   -----------------
   -- Query_Email --
   -----------------

   function Query_Email (Email : Email_Address_Type) return Integer
   is
   begin
      for Ent of Database loop
         if Ent.Email.all = Email then
            return Ent.Key;
         end if;
      end loop;
      return 0;
   end Query_Email;

end Database;
