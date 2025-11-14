package P with SPARK_Mode is

   --  Dummy record type, to make sure we produce data representation file

   type T is record
      C : Integer;
   end record;

   --  Dummy routine, to make sure we generate at least one VC

   function F (X, Y : T) return T is (T'(C => X.C / Y.C))
     with Pre => Y.C not in 0 | -1;
end;
