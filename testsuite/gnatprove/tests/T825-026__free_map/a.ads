package A with SPARK_Mode is
    type Map;
    type Map_Acc is access Map;
    type Element_Acc is not null access Integer;
    type Map is record
       Key   : Positive;
       Value : Element_Acc;
       Next  : Map_Acc;
    end record;
    type Structure is record
       Map_field : Map_Acc;
    end record;

    procedure Free_Mem (S : in out Structure);
    --  with Depends => (S => null, null => S);
end A;
