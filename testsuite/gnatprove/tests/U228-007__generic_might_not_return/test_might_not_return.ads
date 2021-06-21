package Test_Might_Not_Return is

    type Ghost_State is (Init, Config, Run) with Ghost;
    State : Ghost_State := Init with Ghost;

    procedure Die with No_Return;
    procedure Entrance_Check with Annotate => (GNATprove, Might_Not_Return);

    procedure Init with
        Post => State = Init;

    generic
    procedure Set_Something_Gen with
        Pre => State = Init,
        Post => State = Config,
        Annotate => (GNATprove, Might_Not_Return);

    generic
    procedure Run_Gen with
        Pre => State = Config,
        Post => State = Run,
        Annotate => (GNATprove, Might_Not_Return);

end Test_Might_Not_Return;
