procedure Relaxed_Initialization with SPARK_Mode is
   subtype My_Float is Float range 1.0 .. Float (Integer'Last);
   subtype My_Duration is Duration range 0.0 .. 60.0;

     type Rec (D : Boolean := False) is record
        X : Positive;
      case D is
         when True =>   Y : My_Float;
         when False  => Z : My_Duration;
      end case;
     end record with Relaxed_Initialization
;


     type Vec is array (Positive range <>) of Rec;

     --  Initialize all but the X components of Obj. X has to be an in out
     --  parameter as the discriminants of its components are read.
     procedure Partially_Init (Obj : in out Vec)
     with Pre => (for all Elem of Obj => Elem.D'Initialized),
       Post => (for all Elem of Obj =>
                  Elem.D'Initialized and then
                    (if Elem.D
                     then Elem.Y'Initialized
                     else Elem.Z'Initialized and Elem.Z = 0.0));

     procedure Partially_Init (Obj : in out Vec) is
     begin
        for Idx in Obj'Range loop
         if Obj (Idx).D then
            Obj (Idx).Y := Float (Idx);
         else
            Obj (Idx).Z := 0.0;
         end if;

         pragma Loop_Invariant
           ((for all Elem of Obj (Obj'First .. Idx) =>
              Elem.D'Initialized and then
              (if Elem.D
               then Elem.Y'Initialized
               else Elem.Z'Initialized and Elem.Z = 0.0)));
        end loop;
     end Partially_Init;

     procedure Init_X_Components (Obj : in out Vec)
       with Post => (for all Idx in Obj'Range =>
                       Obj (Idx)'Initialized and
                       Obj (Idx) = Obj'Old (Idx)'Update (X => 1)),
     Pre => (for all Idx in Obj'Range =>
               Obj (Idx).D'Initialized and then
               (if Obj (Idx).D then Obj (Idx).Y'Initialized
                else Obj (Idx).Z'Initialized))
     is
     begin
        for Idx in Obj'Range loop
           Obj (Idx).X := 1;

           pragma Loop_Invariant
             (for all Idx2 in Obj'First .. Idx =>
                (Obj (Idx2)'Initialized and
                 Obj (Idx2) = Obj'Loop_Entry (Idx2)'Update (X => 1)));
        end loop;
     end;

   Rec_True  : Rec (True);
   Rec_False : Rec (False);
   Obj       : Vec := (1 | 3 | 5 => Rec_True,
                       2 | 4     => Rec_False);
begin
    Partially_Init (Obj);
    Init_X_Components (Obj);
    pragma Assert (for all E of Obj => E'Initialized);
end;
