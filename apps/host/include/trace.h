#pragma once

#ifdef TRACE_MODE
#include <spdlog/spdlog.h>
#include <string>
#include <ostream>
#include <iomanip>

#define TRACE_INFO(...) spdlog::info(__VA_ARGS__)
#define TRACE_ERROR(...) spdlog::error(__VA_ARGS__)
#define TRACE_DEBUG(...) spdlog::debug(__VA_ARGS__)
#define TRACE_WARN(...) spdlog::warn(__VA_ARGS__)

#define LOG_LEVEL_INFO spdlog::set_level(spdlog::level::info)
#define LOG_LEVEL_DEBUG spdlog::set_level(spdlog::level::debug)
#define LOG_LEVEL_WARN spdlog::set_level(spdlog::level::warn)

#else

#define TRACE_INFO(...)
#define TRACE_ERROR(...)
#define TRACE_DEBUG(...)
#define TRACE_WARN(...)

#define LOG_LEVEL_INFO
#define LOG_LEVEL_DEBUG
#define LOG_LEVEL_WARN

#endif
