const std = @import("std");

pub fn buildFadec(b: *std.Build, comptime path:[]const u8) !*std.Build.Step {
    const step = b.step("build fadec", "");

    try step.evalChildProcess(&[_][]const u8{"meson", "setup", path ++ "/build", path});
    try step.evalChildProcess(&[_][]const u8{"meson", "compile", "-C", path ++ "/build"});
    return step;
}

pub fn build(b: *std.Build) !void {
    const exe = b.addExecutable(.{
        .name = "re",
        .root_source_file = .{ .path = "re.zig" },
    });
    b.installArtifact(exe);

    const run_fresh_step = std.build.RunStep.create(b, "run fresh");
    run_fresh_step.addArtifactArg(exe);

    b.step("run", "runs zig-re's main (currently just for testing purposes)").dependOn(&run_fresh_step.step);

    const test_step = b.step("test", "Run unit tests");

    const unit_tests = b.addTest(.{
        .root_source_file = .{ .path = "re.zig" },
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);
    test_step.dependOn(&run_unit_tests.step);



    const fadecRoot = std.Build.LazyPath.relative("thirdparty/fadec");
    const fadecBuild = std.Build.LazyPath.relative("thirdparty/fadec/build");
    const fadecBuildLibarchive = std.Build.LazyPath.relative("thirdparty/fadec/build/libfadec.a");

    const fadecBuildStep = try buildFadec(b, "thirdparty/fadec");

    for([_]*std.Build.Step.Compile{exe, unit_tests}) |compileStep| {
        compileStep.addIncludePath(fadecRoot);
        compileStep.addIncludePath(fadecBuild);

        compileStep.addLibraryPath(fadecBuild);

        compileStep.addObjectFile(fadecBuildLibarchive);

        compileStep.linkLibC();
        compileStep.step.dependOn(fadecBuildStep);
    }
}
