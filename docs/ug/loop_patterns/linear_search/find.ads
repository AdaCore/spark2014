package Find
  with SPARK_Mode
is

   Max : constant := 300;

  type Opt_Ident_T is new Short_Integer range
     0 .. Max;

   subtype Ident_T is Opt_Ident_T range
     1 .. Opt_Ident_T'Last;

   Null_Ident : constant Opt_Ident_T := 0;

   type Data_T is
        (Default, Green, Red);

   type Opt_Data_T is record
      Exists : Boolean;
      Data  : Data_T;
   end record;

   Null_Data : constant Opt_Data_T := Opt_Data_T'
     (Exists => False,
      Data   => Default);

   type Table_T is array (Ident_T) of Opt_Data_T;

   function Find_Slot (Table        : Table_T;
                       Search_Start : Ident_T) return Opt_Ident_T with
             --  The found slot fulfills the search criterion (not exists).
     Post => (if Find_Slot'Result in Ident_T then
                not Table (Find_Slot'Result). Exists);

end Find;
