const std = @import("std");

const fadecRootS = "thirdparty/fadec";
const fadecBuildS = fadecRootS ++ "/build";
const debugModeDirPathS = "tmp/zig-build-include";

const rootSourceFile = "re.zig";

pub fn buildFadec(step: *std.Build.Step, _:std.Progress.Node) anyerror!void {
    try step.evalChildProcess(&[_][]const u8{"meson", "setup", fadecBuildS, fadecRootS});
    try step.evalChildProcess(&[_][]const u8{"meson", "compile", "-C", fadecBuildS});
}

// TODO this is a ridiculously stupid solution to a problem which should be easy - find a better one
// TODO another problem of this solution is that there's no easy way to delete the temp directory again after building
pub fn createDebugModeFile(step: *std.Build.Step) !void {
    try step.evalChildProcess(&[_][]const u8{"mkdir", "-p", debugModeDirPathS});
    try step.evalChildProcess(&[_][]const u8{"bash", "-c", "echo 'pub const debug = true;' > " ++ debugModeDirPathS ++ "/mode.zig"});
}

pub fn createReleaseModeFile(step: *std.Build.Step) !void {
    try step.evalChildProcess(&[_][]const u8{"mkdir", "-p", debugModeDirPathS});
    try step.evalChildProcess(&[_][]const u8{"bash", "-c", "echo 'pub const debug = false;' > " ++ debugModeDirPathS ++ "/mode.zig"});
}

pub fn clean(clean_step: *std.Build.Step, _:std.Progress.Node) anyerror!void {
    const b = clean_step.owner;
    // run meson clean in fadec root
    try clean_step.evalChildProcess(&[_][]const u8{"meson", "compile", "-C", fadecBuildS,  "--clean"});
    // remove zig-out
    clean_step.dependOn(&b.addRemoveDirTree(b.install_path).step);
    // remove .zig-cache
    // TODO doesn't work anymore with 0.13
    if(b.cache_root.path) |cache_path|
        clean_step.dependOn(&b.addRemoveDirTree(cache_path).step);
}

pub fn build(b: *std.Build) !void {
    const clean_step = b.step("clean", "Remove build artifacts");
    clean_step.makeFn = clean;

    const OptimizeMode = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "re",
        .root_source_file = b.path(rootSourceFile),
        .target = b.standardTargetOptions(.{}),
        .optimize = OptimizeMode,
    });
    b.installArtifact(exe);

    const run_fresh_step = std.Build.Step.Run.create(b, "run fresh");
    run_fresh_step.addArtifactArg(exe);

    if(b.args) |args|
        run_fresh_step.addArgs(args);

    b.step("run", "runs zig-re's main (currently just for testing purposes)").dependOn(&run_fresh_step.step);

    const test_step = b.step("test", "Run unit tests");

    const unit_tests = b.addTest(.{
        .root_source_file = b.path(rootSourceFile),
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

    const debugModeDir = b.path(debugModeDirPathS);

    for([_]*std.Build.Step.Compile{exe, unit_tests}) |compileStep| {
        compileStep.addIncludePath(fadecRoot);
        compileStep.addIncludePath(fadecBuild);
        compileStep.addIncludePath(b.path(debugModeDirPathS));
        try if(OptimizeMode == .Debug)
            createDebugModeFile(&compileStep.step)
        else
            createReleaseModeFile(&compileStep.step);

        const modeModule = b.addModule("mode", std.Build.Module.CreateOptions{.root_source_file = debugModeDir.path(b, "mode.zig"),});
        compileStep.root_module.addImport("mode", modeModule);

        compileStep.addLibraryPath(fadecBuild);

        compileStep.addObjectFile(fadecBuildLibarchive);

        compileStep.linkLibC();
        compileStep.step.dependOn(fadecBuildStep);
    }
}
