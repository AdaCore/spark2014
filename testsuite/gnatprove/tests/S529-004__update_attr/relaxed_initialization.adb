procedure Relaxed_Initialization with SPARK_Mode is
   subtype My_Float is Float range 1.0 .. Float (Integer'Last);
   subtype My_Duration is Duration range 0.0 .. 60.0;

     type Rec (D : Boolean := False) is record
        X : Positive;
      case D is
         when True =>   Y : My_Float;
         when False  => Z : My_Duration;
      end case;
     end record -- with Relaxed_Initialization
;
   pragma Annotate (GNATprove, Init_By_Proof, Rec);

     type Vec is array (Positive range <>) of Rec;

     --  Initialize all but the X components of Obj
     --
     procedure Partially_Init (Obj : out Vec)
       with Post => (for all Elem of Obj =>
                      (if Elem.D
                       then Elem.Y'Valid_Scalars
                       else Elem.Z'Valid_Scalars and Elem.Z = 0.0));

     procedure Partially_Init (Obj : out Vec) is
     begin
        for Idx in Obj'Range loop
         if Obj (Idx).D then
            Obj (Idx).Y := Float (Idx);
         else
            Obj (Idx).Z := 0.0;
         end if;

         pragma Loop_Invariant
           ((for all Elem of Obj (Obj'First .. Idx) =>
              (if Elem.D
               then Elem.Y'Valid_Scalars
               else Elem.Z'Valid_Scalars and Elem.Z = 0.0)));
        end loop;
     end Partially_Init;

     procedure Init_X_Components (Obj : in out Vec)
       with Post => (for all Idx in Obj'Range =>
                       Obj (Idx)'Valid_Scalars and
                       Obj (Idx) = Obj'Old (Idx)'Update (X => 1)),
     Pre => (for all Idx in Obj'Range =>
               (if Obj (Idx).D then Obj (Idx).Y'Valid_Scalars
                else Obj (Idx).Z'Valid_Scalars))
     is
     begin
        for Idx in Obj'Range loop
           Obj (Idx).X := 1;

           pragma Loop_Invariant
             ((for all Idx2 in Obj'First .. Idx =>
                (Obj (Idx2)'Valid_Scalars and
                 Obj (Idx2) = Obj'Loop_Entry (Idx2)'Update (X => 1))));
        end loop;
     end;

   Rec_True  : Rec (True);
   Rec_False : Rec (False);
   Obj       : Vec := (1 | 3 | 5 => Rec_True,
                       2 | 4     => Rec_False);
begin
    Partially_Init (Obj);
    Init_X_Components (Obj);
    pragma Assert (for all E of Obj => E'Valid_Scalars);
end;
