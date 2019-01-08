package Private_Pointer with SPARK_Mode is
    package Mode_On is
       type T is private;
       C_Null : constant T;
       function Is_Null (X : T) return Boolean;
    private
       type T is access Integer;
       C_Null : constant T := null;
       function Is_Null (X : T) return Boolean is (X = null);
    end Mode_On;
    use all type Mode_On.T;

    package Mode_Off is
       type T is private with
         Default_Initial_Condition => Is_Null (T);
       function Is_Null (X : T) return Boolean;
    private
       pragma SPARK_Mode (Off);
       type T is access Integer;
       function Is_Null (X : T) return Boolean is (X = null);
    end Mode_Off;
    use all type Mode_Off.T;

    X_1 : Mode_On.T;
    pragma Assert (X_1 = Mode_On.C_Null);
    pragma Assert (Is_Null (X_1));
    X_2 : Mode_Off.T;
    pragma Assert (Is_Null (X_2));
end Private_Pointer;
