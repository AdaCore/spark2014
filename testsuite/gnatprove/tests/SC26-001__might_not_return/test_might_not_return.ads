package Test_Might_Not_Return is

    type Ghost_State is (Init, Config, Run) with Ghost;
    State : Ghost_State := Init with Ghost;

    procedure Die with No_Return;
    procedure Entrance_Check with Always_Terminates => False;

    procedure Init with
        Post => State = Init;

    procedure Set_Something with
        Pre => State = Init,
        Post => State = Config,
        Always_Terminates => False;

    procedure Run with
        Pre => State = Config,
        Post => State = Run,
        Always_Terminates => False;

end Test_Might_Not_Return;
