package io.github.jmltoolkit.lsp

import io.github.jmltoolkit.lsp.project.Project
import io.github.jmltoolkit.lsp.project.ProjectDefinition
import java.nio.file.Path
import java.nio.file.StandardWatchEventKinds
import java.nio.file.WatchService

class ProjectDefinitionService {
    private var rootFolders: List<Path> = listOf()
    private var configFiles: List<Path> = listOf()

    private var config: MutableMap<Path, ProjectDefinition> = hashMapOf()

    private var backgroundThread: Thread? = null

    fun get(path: Path): ProjectDefinition? {
        var cp: Path? = path
        while (cp != null && cp != cp.root && cp !in configFiles) {
            cp = cp.parent
        }

        synchronized(config) {
            return config[path]
        }
    }

    fun update(workspaceFolders: List<Uri>) {
        removeWatchers()
        synchronized(config) {
            rootFolders = workspaceFolders.map { it.path }
            configFiles = rootFolders.map { Project.create(it) }
            config = configFiles.associateWith { Project.read(it) }.toMutableMap()
        }
        newWatchers()
    }

    private fun removeWatchers() {
        backgroundThread?.interrupt()
    }

    private fun newWatchers() {
        val fs = rootFolders.firstOrNull()?.fileSystem
        if (fs != null) {
            val ws = fs.newWatchService()
            configFiles.map {
                it.parent.register(ws, StandardWatchEventKinds.ENTRY_MODIFY)
            }
            backgroundThread = Thread(Watcher(ws)).also { it.start() }
        }
    }

    private fun updateConfig(configPath: Path) {
        synchronized(config) {
            config[configPath] = Project.read(configPath)
        }
    }


    inner class Watcher(
        private var ws: WatchService
    ) : Runnable {
        override fun run() {
            ws.use {
                while (!Thread.interrupted()) {
                    ws.poll()?.let { key ->
                        for (pollEvent in key.pollEvents()) {
                            val configPath = pollEvent.context() as Path
                            updateConfig(configPath)
                        }
                        key.reset()
                    }
                }
            }
        }
    }
}
