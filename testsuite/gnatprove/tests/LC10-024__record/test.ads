package Test is

   type T is private;
   N : constant Integer;

   function Get_Remaining (S : T) return Integer;

   procedure Next (S : in out T)
   with Post => Get_Remaining (S) = Get_Remaining (S'Old);

   procedure P (S : in out T)
   with Pre  => Get_Remaining (S) > 0,
        Post => Get_Remaining(S) <= Get_Remaining(S'Old);

private
   N : constant Integer := 5;

   type Length_Type is range 0 .. N;

   type Entry_Id is mod N;

   type A is array (Entry_Id) of Integer;

   type T is record
      Remaining : Length_Type;
      Index     : Entry_Id;
      Cards     : A;
   end record;

   function Get_Remaining (S : T) return Integer is
     (Integer(S.Remaining));

end Test;
