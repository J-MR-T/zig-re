const std = @import("std");

const fadecRootS = "thirdparty/fadec";
const fadecBuildS = fadecRootS ++ "/build";

const rootSourceFile = "re.zig";

pub fn buildFadec(step: *std.Build.Step, _:*std.Progress.Node) anyerror!void {
    try step.evalChildProcess(&[_][]const u8{"meson", "setup", fadecBuildS, fadecRootS});
    try step.evalChildProcess(&[_][]const u8{"meson", "compile", "-C", fadecBuildS});
}

pub fn clean(clean_step: *std.Build.Step, _:*std.Progress.Node) anyerror!void {
    const b = clean_step.owner;
    // run meson clean in fadec root
    try clean_step.evalChildProcess(&[_][]const u8{"meson", "compile", "-C", fadecBuildS,  "--clean"});
    // remove zig-out
    clean_step.dependOn(&b.addRemoveDirTree(b.install_path).step);
    // remove zig-cache
    if(b.cache_root.path) |cache_path|
        clean_step.dependOn(&b.addRemoveDirTree(cache_path).step);
}

pub fn build(b: *std.Build) !void {
    const clean_step = b.step("clean", "Remove build artifacts");
    clean_step.makeFn = clean;

    const exe = b.addExecutable(.{
        .name = "re",
        .root_source_file = .{ .path = rootSourceFile},
        .target = b.standardTargetOptions(.{}),
        .optimize = b.standardOptimizeOption(.{}),
    });
    b.installArtifact(exe);

    const run_fresh_step = std.Build.Step.Run.create(b, "run fresh");
    run_fresh_step.addArtifactArg(exe);

    b.step("run", "runs zig-re's main (currently just for testing purposes)").dependOn(&run_fresh_step.step);

    const test_step = b.step("test", "Run unit tests");

    const unit_tests = b.addTest(.{
        .root_source_file = .{ .path = rootSourceFile},
        .filters = if(b.args) |args| 
            args
        else &[_][]const u8{},
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);
    test_step.dependOn(&run_unit_tests.step);

    const fadecRoot = b.path(fadecRootS);
    const fadecBuild = b.path(fadecBuildS);
    const fadecBuildLibarchive = b.path(fadecBuildS ++ "/libfadec.a");

    const fadecBuildStep = b.step("build fadec", "");
    fadecBuildStep.makeFn = buildFadec;

    for([_]*std.Build.Step.Compile{exe, unit_tests}) |compileStep| {
        compileStep.addIncludePath(fadecRoot);
        compileStep.addIncludePath(fadecBuild);

        compileStep.addLibraryPath(fadecBuild);

        compileStep.addObjectFile(fadecBuildLibarchive);

        compileStep.linkLibC();
        compileStep.step.dependOn(fadecBuildStep);
    }
}
